// Lean compiler output
// Module: Lean.Meta.Structure
// Imports: public import Lean.AddDecl public import Lean.Meta.AppBuilder import Lean.Structure import Lean.Meta.Transform
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_isOutParam(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_addProjectionFnInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_updateForallBinderInfos(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVarsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getStructureName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_getStructureName___closed__0 = (const lean_object*)&l_Lean_Meta_getStructureName___closed__0_value;
static lean_once_cell_t l_Lean_Meta_getStructureName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getStructureName___closed__1;
static const lean_string_object l_Lean_Meta_getStructureName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not a structure"};
static const lean_object* l_Lean_Meta_getStructureName___closed__2 = (const lean_object*)&l_Lean_Meta_getStructureName___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getStructureName___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getStructureName___closed__3;
static const lean_string_object l_Lean_Meta_getStructureName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "expected structure"};
static const lean_object* l_Lean_Meta_getStructureName___closed__4 = (const lean_object*)&l_Lean_Meta_getStructureName___closed__4_value;
static lean_once_cell_t l_Lean_Meta_getStructureName___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getStructureName___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to generate projection `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`, not enough constructor fields"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` for the 'Prop'-valued type `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`, field must be a proof, but it has type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`, too many structure parameter overrides"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkProjections___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l_Lean_Meta_mkProjections___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkProjections___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkProjections___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l_Lean_Meta_mkProjections___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_mkProjections___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "projection generation failed, `"};
static const lean_object* l_Lean_Meta_mkProjections___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkProjections___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_mkProjections___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` is an ill-formed inductive datatype"};
static const lean_object* l_Lean_Meta_mkProjections___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkProjections___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkProjections___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "cannot generate projections for `"};
static const lean_object* l_Lean_Meta_mkProjections___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkProjections___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_mkProjections___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`, does not have exactly one constructor"};
static const lean_object* l_Lean_Meta_mkProjections___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_mkProjections___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkProjections___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkProjections___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___closed__0;
static lean_once_cell_t l_Lean_Meta_mkProjections___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___closed__1;
static lean_once_cell_t l_Lean_Meta_mkProjections___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___closed__2;
static lean_once_cell_t l_Lean_Meta_mkProjections___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___closed__3;
static lean_once_cell_t l_Lean_Meta_mkProjections___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkProjections___closed__4;
static const lean_array_object l_Lean_Meta_mkProjections___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkProjections___closed__5 = (const lean_object*)&l_Lean_Meta_mkProjections___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_etaStructReduce___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_etaStructReduce___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_etaStructReduce___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_etaStructReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaStructReduce___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_etaStructReduce___closed__0 = (const lean_object*)&l_Lean_Meta_etaStructReduce___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.Structure"};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0_value;
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.instantiateStructDefaultValueFn\?"};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1_value;
static const lean_string_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "assertion violation: us.length == cinfo.levelParams.length\n  "};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2_value;
static lean_once_cell_t l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__3(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__2));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__4));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName(lean_object* v_struct_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Expr_getAppFn(v_struct_56_);
if (lean_obj_tag(v___x_62_) == 4)
{
lean_object* v_declName_63_; lean_object* v___x_64_; lean_object* v_env_65_; uint8_t v___x_66_; 
v_declName_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_n(v_declName_63_, 2);
lean_dec_ref_known(v___x_62_, 2);
v___x_64_ = lean_st_ref_get(v_a_60_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
v___x_66_ = l_Lean_isStructure(v_env_65_, v_declName_63_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v___x_67_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_68_ = l_Lean_MessageData_ofConstName(v_declName_63_, v___x_66_);
v___x_69_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__3, &l_Lean_Meta_getStructureName___closed__3_once, _init_l_Lean_Meta_getStructureName___closed__3);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_71_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v_declName_63_);
return v___x_81_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v___x_62_);
v___x_82_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__5, &l_Lean_Meta_getStructureName___closed__5_once, _init_l_Lean_Meta_getStructureName___closed__5);
v___x_83_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_82_, v_a_57_, v_a_58_, v_a_59_, v_a_60_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName___boxed(lean_object* v_struct_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_getStructureName(v_struct_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_struct_84_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_object* v_00_u03b1_91_, lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(lean_object* v_00_u03b1_99_, lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(v_00_u03b1_99_, v_msg_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(lean_object* v_name_107_, lean_object* v_levelParams_108_, lean_object* v_type_109_, lean_object* v_value_110_, lean_object* v_hints_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; uint8_t v___y_116_; uint8_t v___y_123_; lean_object* v_env_126_; uint8_t v___x_127_; 
v___x_114_ = lean_st_ref_get(v___y_112_);
v_env_126_ = lean_ctor_get(v___x_114_, 0);
lean_inc_ref_n(v_env_126_, 2);
lean_dec(v___x_114_);
v___x_127_ = l_Lean_Environment_hasUnsafe(v_env_126_, v_type_109_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = l_Lean_Environment_hasUnsafe(v_env_126_, v_value_110_);
v___y_123_ = v___x_128_;
goto v___jp_122_;
}
else
{
lean_dec_ref(v_env_126_);
v___y_123_ = v___x_127_;
goto v___jp_122_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_inc(v_name_107_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_name_107_);
lean_ctor_set(v___x_117_, 1, v_levelParams_108_);
lean_ctor_set(v___x_117_, 2, v_type_109_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v_name_107_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v_value_110_);
lean_ctor_set(v___x_120_, 2, v_hints_111_);
lean_ctor_set(v___x_120_, 3, v___x_119_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*4, v___y_116_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
v___jp_122_:
{
if (v___y_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 1;
v___y_116_ = v___x_124_;
goto v___jp_115_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
v___y_116_ = v___x_125_;
goto v___jp_115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v_name_129_, lean_object* v_levelParams_130_, lean_object* v_type_131_, lean_object* v_value_132_, lean_object* v_hints_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_129_, v_levelParams_130_, v_type_131_, v_value_132_, v_hints_133_, v___y_134_);
lean_dec(v___y_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_name_137_, lean_object* v_levelParams_138_, lean_object* v_type_139_, lean_object* v_value_140_, lean_object* v_hints_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_137_, v_levelParams_138_, v_type_139_, v_value_140_, v_hints_141_, v___y_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object* v_name_148_, lean_object* v_levelParams_149_, lean_object* v_type_150_, lean_object* v_value_151_, lean_object* v_hints_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_148_, v_levelParams_149_, v_type_150_, v_value_151_, v_hints_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v_k_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
v___x_166_ = lean_apply_6(v_k_159_, v_b_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_167_, lean_object* v_b_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_167_, v_b_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_name_175_, uint8_t v_bi_176_, lean_object* v_type_177_, lean_object* v_k_178_, uint8_t v_kind_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; 
v___f_185_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_185_, 0, v_k_178_);
v___x_186_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_175_, v_bi_176_, v_type_177_, v___f_185_, v_kind_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_186_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_186_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object* v_name_203_, lean_object* v_bi_204_, lean_object* v_type_205_, lean_object* v_k_206_, lean_object* v_kind_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
uint8_t v_bi_boxed_213_; uint8_t v_kind_boxed_214_; lean_object* v_res_215_; 
v_bi_boxed_213_ = lean_unbox(v_bi_204_);
v_kind_boxed_214_ = lean_unbox(v_kind_207_);
v_res_215_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_203_, v_bi_boxed_213_, v_type_205_, v_k_206_, v_kind_boxed_214_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_00_u03b1_216_, lean_object* v_name_217_, uint8_t v_bi_218_, lean_object* v_type_219_, lean_object* v_k_220_, uint8_t v_kind_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_217_, v_bi_218_, v_type_219_, v_k_220_, v_kind_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object* v_00_u03b1_228_, lean_object* v_name_229_, lean_object* v_bi_230_, lean_object* v_type_231_, lean_object* v_k_232_, lean_object* v_kind_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
uint8_t v_bi_boxed_239_; uint8_t v_kind_boxed_240_; lean_object* v_res_241_; 
v_bi_boxed_239_ = lean_unbox(v_bi_230_);
v_kind_boxed_240_ = lean_unbox(v_kind_233_);
v_res_241_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(v_00_u03b1_228_, v_name_229_, v_bi_boxed_239_, v_type_231_, v_k_232_, v_kind_boxed_240_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_242_, lean_object* v_b_243_, lean_object* v_c_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
v___x_250_ = lean_apply_7(v_k_242_, v_b_243_, v_c_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_251_, lean_object* v_b_252_, lean_object* v_c_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_251_, v_b_252_, v_c_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_type_260_, lean_object* v_maxFVars_x3f_261_, lean_object* v_k_262_, uint8_t v_cleanupAnnotations_263_, uint8_t v_whnfType_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___f_270_; lean_object* v___x_271_; 
v___f_270_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_270_, 0, v_k_262_);
v___x_271_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_260_, v_maxFVars_x3f_261_, v___f_270_, v_cleanupAnnotations_263_, v_whnfType_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_a_280_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_271_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_271_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_type_288_, lean_object* v_maxFVars_x3f_289_, lean_object* v_k_290_, lean_object* v_cleanupAnnotations_291_, lean_object* v_whnfType_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_298_; uint8_t v_whnfType_boxed_299_; lean_object* v_res_300_; 
v_cleanupAnnotations_boxed_298_ = lean_unbox(v_cleanupAnnotations_291_);
v_whnfType_boxed_299_ = lean_unbox(v_whnfType_292_);
v_res_300_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_288_, v_maxFVars_x3f_289_, v_k_290_, v_cleanupAnnotations_boxed_298_, v_whnfType_boxed_299_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_301_, lean_object* v_type_302_, lean_object* v_maxFVars_x3f_303_, lean_object* v_k_304_, uint8_t v_cleanupAnnotations_305_, uint8_t v_whnfType_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_302_, v_maxFVars_x3f_303_, v_k_304_, v_cleanupAnnotations_305_, v_whnfType_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_313_, lean_object* v_type_314_, lean_object* v_maxFVars_x3f_315_, lean_object* v_k_316_, lean_object* v_cleanupAnnotations_317_, lean_object* v_whnfType_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_324_; uint8_t v_whnfType_boxed_325_; lean_object* v_res_326_; 
v_cleanupAnnotations_boxed_324_ = lean_unbox(v_cleanupAnnotations_317_);
v_whnfType_boxed_325_ = lean_unbox(v_whnfType_318_);
v_res_326_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_313_, v_type_314_, v_maxFVars_x3f_315_, v_k_316_, v_cleanupAnnotations_boxed_324_, v_whnfType_boxed_325_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_lctx_327_, lean_object* v_localInsts_328_, lean_object* v_x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_327_, v_localInsts_328_, v_x_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_lctx_352_, lean_object* v_localInsts_353_, lean_object* v_x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_352_, v_localInsts_353_, v_x_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_361_, lean_object* v_lctx_362_, lean_object* v_localInsts_363_, lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_362_, v_localInsts_363_, v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_371_, lean_object* v_lctx_372_, lean_object* v_localInsts_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_371_, v_lctx_372_, v_localInsts_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_fileName_388_; lean_object* v_fileMap_389_; lean_object* v_options_390_; lean_object* v_currRecDepth_391_; lean_object* v_maxRecDepth_392_; lean_object* v_ref_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_initHeartbeats_396_; lean_object* v_maxHeartbeats_397_; lean_object* v_quotContext_398_; lean_object* v_currMacroScope_399_; uint8_t v_diag_400_; lean_object* v_cancelTk_x3f_401_; uint8_t v_suppressElabErrors_402_; lean_object* v_inheritedTraceOptions_403_; lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_fileName_388_ = lean_ctor_get(v___y_385_, 0);
v_fileMap_389_ = lean_ctor_get(v___y_385_, 1);
v_options_390_ = lean_ctor_get(v___y_385_, 2);
v_currRecDepth_391_ = lean_ctor_get(v___y_385_, 3);
v_maxRecDepth_392_ = lean_ctor_get(v___y_385_, 4);
v_ref_393_ = lean_ctor_get(v___y_385_, 5);
v_currNamespace_394_ = lean_ctor_get(v___y_385_, 6);
v_openDecls_395_ = lean_ctor_get(v___y_385_, 7);
v_initHeartbeats_396_ = lean_ctor_get(v___y_385_, 8);
v_maxHeartbeats_397_ = lean_ctor_get(v___y_385_, 9);
v_quotContext_398_ = lean_ctor_get(v___y_385_, 10);
v_currMacroScope_399_ = lean_ctor_get(v___y_385_, 11);
v_diag_400_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*14);
v_cancelTk_x3f_401_ = lean_ctor_get(v___y_385_, 12);
v_suppressElabErrors_402_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_403_ = lean_ctor_get(v___y_385_, 13);
v_ref_404_ = l_Lean_replaceRef(v_ref_381_, v_ref_393_);
lean_inc_ref(v_inheritedTraceOptions_403_);
lean_inc(v_cancelTk_x3f_401_);
lean_inc(v_currMacroScope_399_);
lean_inc(v_quotContext_398_);
lean_inc(v_maxHeartbeats_397_);
lean_inc(v_initHeartbeats_396_);
lean_inc(v_openDecls_395_);
lean_inc(v_currNamespace_394_);
lean_inc(v_maxRecDepth_392_);
lean_inc(v_currRecDepth_391_);
lean_inc_ref(v_options_390_);
lean_inc_ref(v_fileMap_389_);
lean_inc_ref(v_fileName_388_);
v___x_405_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_405_, 0, v_fileName_388_);
lean_ctor_set(v___x_405_, 1, v_fileMap_389_);
lean_ctor_set(v___x_405_, 2, v_options_390_);
lean_ctor_set(v___x_405_, 3, v_currRecDepth_391_);
lean_ctor_set(v___x_405_, 4, v_maxRecDepth_392_);
lean_ctor_set(v___x_405_, 5, v_ref_404_);
lean_ctor_set(v___x_405_, 6, v_currNamespace_394_);
lean_ctor_set(v___x_405_, 7, v_openDecls_395_);
lean_ctor_set(v___x_405_, 8, v_initHeartbeats_396_);
lean_ctor_set(v___x_405_, 9, v_maxHeartbeats_397_);
lean_ctor_set(v___x_405_, 10, v_quotContext_398_);
lean_ctor_set(v___x_405_, 11, v_currMacroScope_399_);
lean_ctor_set(v___x_405_, 12, v_cancelTk_x3f_401_);
lean_ctor_set(v___x_405_, 13, v_inheritedTraceOptions_403_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*14, v_diag_400_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*14 + 1, v_suppressElabErrors_402_);
v___x_406_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_382_, v___y_383_, v___y_384_, v___x_405_, v___y_386_);
lean_dec_ref_known(v___x_405_, 14);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_407_, v_msg_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v_ref_407_);
return v_res_414_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_424_, lean_object* v_projName_425_, lean_object* v_n_426_, lean_object* v_ref_427_, lean_object* v___f_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
if (v___x_424_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_434_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_435_ = l_Lean_MessageData_ofName(v_projName_425_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_MessageData_ofConstName(v_n_426_, v___x_424_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_427_, v___x_442_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
v___x_445_ = lean_apply_6(v___f_428_, v_a_444_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, lean_box(0));
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v___f_428_);
v_a_446_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_443_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_n_426_);
lean_dec(v_projName_425_);
v___x_454_ = lean_box(0);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
v___x_455_ = lean_apply_6(v___f_428_, v___x_454_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, lean_box(0));
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_456_, lean_object* v_projName_457_, lean_object* v_n_458_, lean_object* v_ref_459_, lean_object* v___f_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_18696__boxed_466_; lean_object* v_res_467_; 
v___x_18696__boxed_466_ = lean_unbox(v___x_456_);
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_18696__boxed_466_, v_projName_457_, v_n_458_, v_ref_459_, v___f_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v_ref_459_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_468_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_474_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_ctor_set(v___x_474_, 2, v___x_473_);
lean_ctor_set(v___x_474_, 3, v___x_473_);
lean_ctor_set(v___x_474_, 4, v___x_473_);
lean_ctor_set(v___x_474_, 5, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_475_, uint8_t v_s_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_traceState_485_; lean_object* v_messages_486_; lean_object* v_infoState_487_; lean_object* v_snapshotTasks_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_517_; 
v___x_480_ = lean_st_ref_take(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_480_, 1);
v_ngen_483_ = lean_ctor_get(v___x_480_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_480_, 3);
v_traceState_485_ = lean_ctor_get(v___x_480_, 4);
v_messages_486_ = lean_ctor_get(v___x_480_, 6);
v_infoState_487_ = lean_ctor_get(v___x_480_, 7);
v_snapshotTasks_488_ = lean_ctor_get(v___x_480_, 8);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_480_, 5);
lean_dec(v_unused_518_);
v___x_490_ = v___x_480_;
v_isShared_491_ = v_isSharedCheck_517_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snapshotTasks_488_);
lean_inc(v_infoState_487_);
lean_inc(v_messages_486_);
lean_inc(v_traceState_485_);
lean_inc(v_auxDeclNGen_484_);
lean_inc(v_ngen_483_);
lean_inc(v_nextMacroScope_482_);
lean_inc(v_env_481_);
lean_dec(v___x_480_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_517_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_492_ = 0;
v___x_493_ = lean_box(0);
v___x_494_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_481_, v_declName_475_, v_s_476_, v___x_492_, v___x_493_);
v___x_495_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 5, v___x_495_);
lean_ctor_set(v___x_490_, 0, v___x_494_);
v___x_497_ = v___x_490_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_traceState_485_);
lean_ctor_set(v_reuseFailAlloc_516_, 5, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_516_, 6, v_messages_486_);
lean_ctor_set(v_reuseFailAlloc_516_, 7, v_infoState_487_);
lean_ctor_set(v_reuseFailAlloc_516_, 8, v_snapshotTasks_488_);
v___x_497_ = v_reuseFailAlloc_516_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_mctx_500_; lean_object* v_zetaDeltaFVarIds_501_; lean_object* v_postponed_502_; lean_object* v_diag_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_514_; 
v___x_498_ = lean_st_ref_put(v___y_478_, v___x_497_);
v___x_499_ = lean_st_ref_take(v___y_477_);
v_mctx_500_ = lean_ctor_get(v___x_499_, 0);
v_zetaDeltaFVarIds_501_ = lean_ctor_get(v___x_499_, 2);
v_postponed_502_ = lean_ctor_get(v___x_499_, 3);
v_diag_503_ = lean_ctor_get(v___x_499_, 4);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_499_, 1);
lean_dec(v_unused_515_);
v___x_505_ = v___x_499_;
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_diag_503_);
lean_inc(v_postponed_502_);
lean_inc(v_zetaDeltaFVarIds_501_);
lean_inc(v_mctx_500_);
lean_dec(v___x_499_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_mctx_500_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_zetaDeltaFVarIds_501_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_postponed_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_diag_503_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_st_ref_put(v___y_477_, v___x_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_519_, lean_object* v_s_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v_s_boxed_524_; lean_object* v_res_525_; 
v_s_boxed_524_ = lean_unbox(v_s_520_);
v_res_525_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_519_, v_s_boxed_524_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v___x_532_; lean_object* v___x_533_; 
v___x_532_ = 0;
v___x_533_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_526_, v___x_532_, v___y_528_, v___y_530_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_550_, lean_object* v_projName_551_, lean_object* v___x_552_, lean_object* v_a_553_, uint8_t v_instImplicit_554_, lean_object* v___x_555_, lean_object* v_params_556_, lean_object* v_self_557_, lean_object* v_b_558_, uint8_t v___x_559_, lean_object* v_a_560_, lean_object* v___x_561_, lean_object* v_paramInfoOverrides_562_, lean_object* v_n_563_, lean_object* v_ref_564_, lean_object* v___x_565_, uint8_t v_a_566_, lean_object* v_____r_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_643_; uint8_t v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = l_List_lengthTR___redArg(v_paramInfoOverrides_562_);
v___x_737_ = lean_array_get_size(v_params_556_);
v___x_738_ = lean_nat_dec_le(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_739_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_551_);
v___x_740_ = l_Lean_MessageData_ofName(v_projName_551_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc(v_n_563_);
v___x_744_ = l_Lean_MessageData_ofConstName(v_n_563_, v___x_738_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_564_, v___x_747_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
goto v___jp_697_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
goto v___jp_697_;
}
v___jp_573_:
{
lean_object* v___x_576_; lean_object* v_env_577_; lean_object* v_nextMacroScope_578_; lean_object* v_ngen_579_; lean_object* v_auxDeclNGen_580_; lean_object* v_traceState_581_; lean_object* v_messages_582_; lean_object* v_infoState_583_; lean_object* v_snapshotTasks_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_616_; 
v___x_576_ = lean_st_ref_take(v___y_574_);
v_env_577_ = lean_ctor_get(v___x_576_, 0);
v_nextMacroScope_578_ = lean_ctor_get(v___x_576_, 1);
v_ngen_579_ = lean_ctor_get(v___x_576_, 2);
v_auxDeclNGen_580_ = lean_ctor_get(v___x_576_, 3);
v_traceState_581_ = lean_ctor_get(v___x_576_, 4);
v_messages_582_ = lean_ctor_get(v___x_576_, 6);
v_infoState_583_ = lean_ctor_get(v___x_576_, 7);
v_snapshotTasks_584_ = lean_ctor_get(v___x_576_, 8);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_576_, 5);
lean_dec(v_unused_617_);
v___x_586_ = v___x_576_;
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snapshotTasks_584_);
lean_inc(v_infoState_583_);
lean_inc(v_messages_582_);
lean_inc(v_traceState_581_);
lean_inc(v_auxDeclNGen_580_);
lean_inc(v_ngen_579_);
lean_inc(v_nextMacroScope_578_);
lean_inc(v_env_577_);
lean_dec(v___x_576_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_616_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_name_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v_name_588_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_name_588_);
lean_dec_ref(v___x_550_);
lean_inc(v_projName_551_);
v___x_589_ = l_Lean_addProjectionFnInfo(v_env_577_, v_projName_551_, v_name_588_, v___x_552_, v_a_553_, v_instImplicit_554_);
v___x_590_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 5, v___x_590_);
lean_ctor_set(v___x_586_, 0, v___x_589_);
v___x_592_ = v___x_586_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_nextMacroScope_578_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_ngen_579_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_auxDeclNGen_580_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_traceState_581_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_messages_582_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_infoState_583_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_snapshotTasks_584_);
v___x_592_ = v_reuseFailAlloc_615_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_mctx_595_; lean_object* v_zetaDeltaFVarIds_596_; lean_object* v_postponed_597_; lean_object* v_diag_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_613_; 
v___x_593_ = lean_st_ref_put(v___y_574_, v___x_592_);
v___x_594_ = lean_st_ref_take(v___y_575_);
v_mctx_595_ = lean_ctor_get(v___x_594_, 0);
v_zetaDeltaFVarIds_596_ = lean_ctor_get(v___x_594_, 2);
v_postponed_597_ = lean_ctor_get(v___x_594_, 3);
v_diag_598_ = lean_ctor_get(v___x_594_, 4);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_594_, 1);
lean_dec(v_unused_614_);
v___x_600_ = v___x_594_;
v_isShared_601_ = v_isSharedCheck_613_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_diag_598_);
lean_inc(v_postponed_597_);
lean_inc(v_zetaDeltaFVarIds_596_);
lean_inc(v_mctx_595_);
lean_dec(v___x_594_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_613_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_mctx_595_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_zetaDeltaFVarIds_596_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_postponed_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_diag_598_);
v___x_604_ = v_reuseFailAlloc_612_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_605_ = lean_st_ref_put(v___y_575_, v___x_604_);
v___x_606_ = l_Lean_Expr_const___override(v_projName_551_, v___x_555_);
v___x_607_ = l_Lean_mkAppN(v___x_606_, v_params_556_);
v___x_608_ = l_Lean_Expr_app___override(v___x_607_, v_self_557_);
v___x_609_ = l_Lean_Expr_bindingBody_x21(v_b_558_);
v___x_610_ = lean_expr_instantiate1(v___x_609_, v___x_608_);
lean_dec_ref(v___x_608_);
lean_dec_ref(v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
}
}
v___jp_618_:
{
if (lean_obj_tag(v___y_621_) == 0)
{
lean_dec_ref_known(v___y_621_, 1);
v___y_574_ = v___y_619_;
v___y_575_ = v___y_620_;
goto v___jp_573_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_622_ = lean_ctor_get(v___y_621_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___y_621_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___y_621_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___y_621_);
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
v___jp_630_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = lean_box(0);
lean_inc(v_projName_551_);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v_projName_551_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_639_, 0, v___y_632_);
lean_ctor_set(v___x_639_, 1, v___y_631_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*3, v___x_559_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = l_Lean_addDecl(v___x_640_, v___y_634_, v___y_635_, v___y_633_);
lean_dec_ref(v___y_635_);
v___y_619_ = v___y_633_;
v___y_620_ = v___y_636_;
v___y_621_ = v___x_641_;
goto v___jp_618_;
}
v___jp_642_:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v_fileName_651_; lean_object* v_fileMap_652_; lean_object* v_options_653_; lean_object* v_currRecDepth_654_; lean_object* v_maxRecDepth_655_; lean_object* v_ref_656_; lean_object* v_currNamespace_657_; lean_object* v_openDecls_658_; lean_object* v_initHeartbeats_659_; lean_object* v_maxHeartbeats_660_; lean_object* v_quotContext_661_; lean_object* v_currMacroScope_662_; uint8_t v_diag_663_; lean_object* v_cancelTk_x3f_664_; uint8_t v_suppressElabErrors_665_; lean_object* v_inheritedTraceOptions_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_ref_671_; lean_object* v___x_672_; 
v___x_649_ = 0;
lean_inc_ref(v_a_560_);
v___x_650_ = l_Lean_LocalContext_mkForall(v_a_560_, v___x_561_, v___y_643_, v___x_559_, v___x_649_);
lean_dec_ref(v___y_643_);
v_fileName_651_ = lean_ctor_get(v___y_647_, 0);
v_fileMap_652_ = lean_ctor_get(v___y_647_, 1);
v_options_653_ = lean_ctor_get(v___y_647_, 2);
v_currRecDepth_654_ = lean_ctor_get(v___y_647_, 3);
v_maxRecDepth_655_ = lean_ctor_get(v___y_647_, 4);
v_ref_656_ = lean_ctor_get(v___y_647_, 5);
v_currNamespace_657_ = lean_ctor_get(v___y_647_, 6);
v_openDecls_658_ = lean_ctor_get(v___y_647_, 7);
v_initHeartbeats_659_ = lean_ctor_get(v___y_647_, 8);
v_maxHeartbeats_660_ = lean_ctor_get(v___y_647_, 9);
v_quotContext_661_ = lean_ctor_get(v___y_647_, 10);
v_currMacroScope_662_ = lean_ctor_get(v___y_647_, 11);
v_diag_663_ = lean_ctor_get_uint8(v___y_647_, sizeof(void*)*14);
v_cancelTk_x3f_664_ = lean_ctor_get(v___y_647_, 12);
v_suppressElabErrors_665_ = lean_ctor_get_uint8(v___y_647_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_666_ = lean_ctor_get(v___y_647_, 13);
v___x_667_ = l_Lean_Expr_inferImplicit(v___x_650_, v___x_552_, v___x_559_);
v___x_668_ = l_Lean_Expr_updateForallBinderInfos(v___x_667_, v_paramInfoOverrides_562_);
lean_inc_ref(v_self_557_);
lean_inc(v_a_553_);
v___x_669_ = l_Lean_Expr_proj___override(v_n_563_, v_a_553_, v_self_557_);
v___x_670_ = l_Lean_LocalContext_mkLambda(v_a_560_, v___x_561_, v___x_669_, v___x_559_, v___x_649_);
lean_dec_ref(v___x_669_);
v_ref_671_ = l_Lean_replaceRef(v_ref_564_, v_ref_656_);
lean_inc_ref(v_inheritedTraceOptions_666_);
lean_inc(v_cancelTk_x3f_664_);
lean_inc(v_currMacroScope_662_);
lean_inc(v_quotContext_661_);
lean_inc(v_maxHeartbeats_660_);
lean_inc(v_initHeartbeats_659_);
lean_inc(v_openDecls_658_);
lean_inc(v_currNamespace_657_);
lean_inc(v_maxRecDepth_655_);
lean_inc(v_currRecDepth_654_);
lean_inc_ref(v_options_653_);
lean_inc_ref(v_fileMap_652_);
lean_inc_ref(v_fileName_651_);
v___x_672_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_672_, 0, v_fileName_651_);
lean_ctor_set(v___x_672_, 1, v_fileMap_652_);
lean_ctor_set(v___x_672_, 2, v_options_653_);
lean_ctor_set(v___x_672_, 3, v_currRecDepth_654_);
lean_ctor_set(v___x_672_, 4, v_maxRecDepth_655_);
lean_ctor_set(v___x_672_, 5, v_ref_671_);
lean_ctor_set(v___x_672_, 6, v_currNamespace_657_);
lean_ctor_set(v___x_672_, 7, v_openDecls_658_);
lean_ctor_set(v___x_672_, 8, v_initHeartbeats_659_);
lean_ctor_set(v___x_672_, 9, v_maxHeartbeats_660_);
lean_ctor_set(v___x_672_, 10, v_quotContext_661_);
lean_ctor_set(v___x_672_, 11, v_currMacroScope_662_);
lean_ctor_set(v___x_672_, 12, v_cancelTk_x3f_664_);
lean_ctor_set(v___x_672_, 13, v_inheritedTraceOptions_666_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*14, v_diag_663_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*14 + 1, v_suppressElabErrors_665_);
if (v___y_644_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(1);
lean_inc(v_projName_551_);
v___x_674_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_551_, v___x_565_, v___x_668_, v___x_670_, v___x_673_, v___y_648_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v_a_675_);
v___x_677_ = l_Lean_addDecl(v___x_676_, v___x_649_, v___x_672_, v___y_648_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_dec_ref_known(v___x_677_, 1);
if (v_instImplicit_554_ == 0)
{
lean_object* v___x_678_; 
lean_inc(v_projName_551_);
v___x_678_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_551_, v___y_645_, v___y_646_, v___x_672_, v___y_648_);
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_678_;
goto v___jp_618_;
}
else
{
lean_dec_ref_known(v___x_672_, 14);
v___y_574_ = v___y_648_;
v___y_575_ = v___y_646_;
goto v___jp_573_;
}
}
else
{
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_677_;
goto v___jp_618_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref_known(v___x_672_, 14);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_679_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_674_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_674_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_687_; lean_object* v_env_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_687_ = lean_st_ref_get(v___y_648_);
v_env_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_ref_n(v_env_688_, 2);
lean_dec(v___x_687_);
lean_inc_ref(v___x_668_);
lean_inc(v_projName_551_);
v___x_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_689_, 0, v_projName_551_);
lean_ctor_set(v___x_689_, 1, v___x_565_);
lean_ctor_set(v___x_689_, 2, v___x_668_);
v___x_690_ = l_Lean_Environment_hasUnsafe(v_env_688_, v___x_668_);
lean_dec_ref(v___x_668_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_Environment_hasUnsafe(v_env_688_, v___x_670_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_692_ = lean_box(0);
lean_inc(v_projName_551_);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v_projName_551_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_689_);
lean_ctor_set(v___x_694_, 1, v___x_670_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
v___x_695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___x_696_ = l_Lean_addDecl(v___x_695_, v___x_649_, v___x_672_, v___y_648_);
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_696_;
goto v___jp_618_;
}
else
{
v___y_631_ = v___x_670_;
v___y_632_ = v___x_689_;
v___y_633_ = v___y_648_;
v___y_634_ = v___x_649_;
v___y_635_ = v___x_672_;
v___y_636_ = v___y_646_;
goto v___jp_630_;
}
}
else
{
lean_dec_ref(v_env_688_);
v___y_631_ = v___x_670_;
v___y_632_ = v___x_689_;
v___y_633_ = v___y_648_;
v___y_634_ = v___x_649_;
v___y_635_ = v___x_672_;
v___y_636_ = v___y_646_;
goto v___jp_630_;
}
}
}
v___jp_697_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = l_Lean_Expr_bindingDomain_x21(v_b_558_);
v___x_699_ = lean_expr_consume_type_annotations(v___x_698_);
lean_inc_ref(v___x_699_);
v___x_700_ = l_Lean_Meta_isProp(v___x_699_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_700_) == 0)
{
if (v_a_566_ == 0)
{
lean_object* v_a_701_; uint8_t v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_unbox(v_a_701_);
lean_dec(v_a_701_);
v___y_643_ = v___x_699_;
v___y_644_ = v___x_702_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
else
{
lean_object* v_a_703_; uint8_t v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_700_, 1);
v___x_704_ = lean_unbox(v_a_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_551_);
v___x_706_ = l_Lean_MessageData_ofName(v_projName_551_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_unbox(v_a_703_);
lean_inc(v_n_563_);
v___x_711_ = l_Lean_MessageData_ofConstName(v_n_563_, v___x_710_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_709_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
lean_inc_ref(v___x_699_);
v___x_715_ = l_Lean_indentExpr(v___x_699_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_564_, v___x_716_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_717_) == 0)
{
uint8_t v___x_718_; 
lean_dec_ref_known(v___x_717_, 1);
v___x_718_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
v___y_643_ = v___x_699_;
v___y_644_ = v___x_718_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_703_);
lean_dec_ref(v___x_699_);
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_719_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
uint8_t v___x_727_; 
v___x_727_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
v___y_643_ = v___x_699_;
v___y_644_ = v___x_727_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___x_699_);
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_728_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_700_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_700_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_757_ = _args[0];
lean_object* v_projName_758_ = _args[1];
lean_object* v___x_759_ = _args[2];
lean_object* v_a_760_ = _args[3];
lean_object* v_instImplicit_761_ = _args[4];
lean_object* v___x_762_ = _args[5];
lean_object* v_params_763_ = _args[6];
lean_object* v_self_764_ = _args[7];
lean_object* v_b_765_ = _args[8];
lean_object* v___x_766_ = _args[9];
lean_object* v_a_767_ = _args[10];
lean_object* v___x_768_ = _args[11];
lean_object* v_paramInfoOverrides_769_ = _args[12];
lean_object* v_n_770_ = _args[13];
lean_object* v_ref_771_ = _args[14];
lean_object* v___x_772_ = _args[15];
lean_object* v_a_773_ = _args[16];
lean_object* v_____r_774_ = _args[17];
lean_object* v___y_775_ = _args[18];
lean_object* v___y_776_ = _args[19];
lean_object* v___y_777_ = _args[20];
lean_object* v___y_778_ = _args[21];
lean_object* v___y_779_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_780_; uint8_t v___x_18935__boxed_781_; uint8_t v_a_18941__boxed_782_; lean_object* v_res_783_; 
v_instImplicit_boxed_780_ = lean_unbox(v_instImplicit_761_);
v___x_18935__boxed_781_ = lean_unbox(v___x_766_);
v_a_18941__boxed_782_ = lean_unbox(v_a_773_);
v_res_783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_757_, v_projName_758_, v___x_759_, v_a_760_, v_instImplicit_boxed_780_, v___x_762_, v_params_763_, v_self_764_, v_b_765_, v___x_18935__boxed_781_, v_a_767_, v___x_768_, v_paramInfoOverrides_769_, v_n_770_, v_ref_771_, v___x_772_, v_a_18941__boxed_782_, v_____r_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v_ref_771_);
lean_dec(v_paramInfoOverrides_769_);
lean_dec_ref(v___x_768_);
lean_dec_ref(v_b_765_);
lean_dec_ref(v_params_763_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_784_, uint8_t v_isExporting_785_, lean_object* v___x_786_, lean_object* v___y_787_, lean_object* v___x_788_, lean_object* v_a_x3f_789_){
_start:
{
lean_object* v___x_791_; lean_object* v_env_792_; lean_object* v_nextMacroScope_793_; lean_object* v_ngen_794_; lean_object* v_auxDeclNGen_795_; lean_object* v_traceState_796_; lean_object* v_messages_797_; lean_object* v_infoState_798_; lean_object* v_snapshotTasks_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_824_; 
v___x_791_ = lean_st_ref_take(v___y_784_);
v_env_792_ = lean_ctor_get(v___x_791_, 0);
v_nextMacroScope_793_ = lean_ctor_get(v___x_791_, 1);
v_ngen_794_ = lean_ctor_get(v___x_791_, 2);
v_auxDeclNGen_795_ = lean_ctor_get(v___x_791_, 3);
v_traceState_796_ = lean_ctor_get(v___x_791_, 4);
v_messages_797_ = lean_ctor_get(v___x_791_, 6);
v_infoState_798_ = lean_ctor_get(v___x_791_, 7);
v_snapshotTasks_799_ = lean_ctor_get(v___x_791_, 8);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_791_, 5);
lean_dec(v_unused_825_);
v___x_801_ = v___x_791_;
v_isShared_802_ = v_isSharedCheck_824_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_snapshotTasks_799_);
lean_inc(v_infoState_798_);
lean_inc(v_messages_797_);
lean_inc(v_traceState_796_);
lean_inc(v_auxDeclNGen_795_);
lean_inc(v_ngen_794_);
lean_inc(v_nextMacroScope_793_);
lean_inc(v_env_792_);
lean_dec(v___x_791_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_824_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = l_Lean_Environment_setExporting(v_env_792_, v_isExporting_785_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 5, v___x_786_);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_nextMacroScope_793_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_ngen_794_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_auxDeclNGen_795_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_traceState_796_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_messages_797_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_infoState_798_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v_snapshotTasks_799_);
v___x_805_ = v_reuseFailAlloc_823_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_mctx_808_; lean_object* v_zetaDeltaFVarIds_809_; lean_object* v_postponed_810_; lean_object* v_diag_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_821_; 
v___x_806_ = lean_st_ref_put(v___y_784_, v___x_805_);
v___x_807_ = lean_st_ref_take(v___y_787_);
v_mctx_808_ = lean_ctor_get(v___x_807_, 0);
v_zetaDeltaFVarIds_809_ = lean_ctor_get(v___x_807_, 2);
v_postponed_810_ = lean_ctor_get(v___x_807_, 3);
v_diag_811_ = lean_ctor_get(v___x_807_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_807_, 1);
lean_dec(v_unused_822_);
v___x_813_ = v___x_807_;
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_diag_811_);
lean_inc(v_postponed_810_);
lean_inc(v_zetaDeltaFVarIds_809_);
lean_inc(v_mctx_808_);
lean_dec(v___x_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_821_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_788_);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_mctx_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_zetaDeltaFVarIds_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_postponed_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_diag_811_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_st_ref_put(v___y_787_, v___x_816_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_826_, lean_object* v_isExporting_827_, lean_object* v___x_828_, lean_object* v___y_829_, lean_object* v___x_830_, lean_object* v_a_x3f_831_, lean_object* v___y_832_){
_start:
{
uint8_t v_isExporting_boxed_833_; lean_object* v_res_834_; 
v_isExporting_boxed_833_ = lean_unbox(v_isExporting_827_);
v_res_834_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_826_, v_isExporting_boxed_833_, v___x_828_, v___y_829_, v___x_830_, v_a_x3f_831_);
lean_dec(v_a_x3f_831_);
lean_dec(v___y_829_);
lean_dec(v___y_826_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_835_, uint8_t v_isExporting_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v_isExporting_844_; lean_object* v___x_910_; uint8_t v_isModule_911_; 
v___x_842_ = lean_st_ref_get(v___y_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v_isExporting_844_ = lean_ctor_get_uint8(v_env_843_, sizeof(void*)*8);
v___x_910_ = l_Lean_Environment_header(v_env_843_);
lean_dec_ref(v_env_843_);
v_isModule_911_ = lean_ctor_get_uint8(v___x_910_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_910_);
if (v_isModule_911_ == 0)
{
lean_object* v___x_912_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v___x_912_ = lean_apply_5(v_x_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
return v___x_912_;
}
else
{
if (v_isExporting_844_ == 0)
{
if (v_isExporting_836_ == 0)
{
lean_object* v___x_913_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v___x_913_ = lean_apply_5(v_x_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
return v___x_913_;
}
else
{
goto v___jp_845_;
}
}
else
{
if (v_isExporting_836_ == 0)
{
goto v___jp_845_;
}
else
{
lean_object* v___x_914_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v___x_914_ = lean_apply_5(v_x_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
return v___x_914_;
}
}
}
v___jp_845_:
{
lean_object* v___x_846_; lean_object* v_env_847_; lean_object* v_nextMacroScope_848_; lean_object* v_ngen_849_; lean_object* v_auxDeclNGen_850_; lean_object* v_traceState_851_; lean_object* v_messages_852_; lean_object* v_infoState_853_; lean_object* v_snapshotTasks_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_908_; 
v___x_846_ = lean_st_ref_take(v___y_840_);
v_env_847_ = lean_ctor_get(v___x_846_, 0);
v_nextMacroScope_848_ = lean_ctor_get(v___x_846_, 1);
v_ngen_849_ = lean_ctor_get(v___x_846_, 2);
v_auxDeclNGen_850_ = lean_ctor_get(v___x_846_, 3);
v_traceState_851_ = lean_ctor_get(v___x_846_, 4);
v_messages_852_ = lean_ctor_get(v___x_846_, 6);
v_infoState_853_ = lean_ctor_get(v___x_846_, 7);
v_snapshotTasks_854_ = lean_ctor_get(v___x_846_, 8);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___x_846_, 5);
lean_dec(v_unused_909_);
v___x_856_ = v___x_846_;
v_isShared_857_ = v_isSharedCheck_908_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snapshotTasks_854_);
lean_inc(v_infoState_853_);
lean_inc(v_messages_852_);
lean_inc(v_traceState_851_);
lean_inc(v_auxDeclNGen_850_);
lean_inc(v_ngen_849_);
lean_inc(v_nextMacroScope_848_);
lean_inc(v_env_847_);
lean_dec(v___x_846_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_908_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = l_Lean_Environment_setExporting(v_env_847_, v_isExporting_836_);
v___x_859_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 5, v___x_859_);
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_nextMacroScope_848_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_ngen_849_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_auxDeclNGen_850_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_traceState_851_);
lean_ctor_set(v_reuseFailAlloc_907_, 5, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_907_, 6, v_messages_852_);
lean_ctor_set(v_reuseFailAlloc_907_, 7, v_infoState_853_);
lean_ctor_set(v_reuseFailAlloc_907_, 8, v_snapshotTasks_854_);
v___x_861_ = v_reuseFailAlloc_907_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_mctx_864_; lean_object* v_zetaDeltaFVarIds_865_; lean_object* v_postponed_866_; lean_object* v_diag_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_905_; 
v___x_862_ = lean_st_ref_put(v___y_840_, v___x_861_);
v___x_863_ = lean_st_ref_take(v___y_838_);
v_mctx_864_ = lean_ctor_get(v___x_863_, 0);
v_zetaDeltaFVarIds_865_ = lean_ctor_get(v___x_863_, 2);
v_postponed_866_ = lean_ctor_get(v___x_863_, 3);
v_diag_867_ = lean_ctor_get(v___x_863_, 4);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_863_, 1);
lean_dec(v_unused_906_);
v___x_869_ = v___x_863_;
v_isShared_870_ = v_isSharedCheck_905_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_diag_867_);
lean_inc(v_postponed_866_);
lean_inc(v_zetaDeltaFVarIds_865_);
lean_inc(v_mctx_864_);
lean_dec(v___x_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_905_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_mctx_864_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_zetaDeltaFVarIds_865_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_postponed_866_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_diag_867_);
v___x_873_ = v_reuseFailAlloc_904_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v_r_875_; 
v___x_874_ = lean_st_ref_put(v___y_838_, v___x_873_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v_r_875_ = lean_apply_5(v_x_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
if (lean_obj_tag(v_r_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_892_; 
v_a_876_ = lean_ctor_get(v_r_875_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_r_875_);
if (v_isSharedCheck_892_ == 0)
{
v___x_878_ = v_r_875_;
v_isShared_879_ = v_isSharedCheck_892_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v_r_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_892_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
lean_inc(v_a_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 1);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_891_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v___x_882_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_840_, v_isExporting_844_, v___x_859_, v___y_838_, v___x_871_, v___x_881_);
lean_dec_ref(v___x_881_);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_890_);
v___x_884_ = v___x_882_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_dec(v___x_882_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v_a_876_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_876_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_893_ = lean_ctor_get(v_r_875_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v_r_875_, 1);
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_840_, v_isExporting_844_, v___x_859_, v___y_838_, v___x_871_, v___x_894_);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_903_);
v___x_897_ = v___x_895_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_dec(v___x_895_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 1);
lean_ctor_set(v___x_897_, 0, v_a_893_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_893_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_915_, lean_object* v_isExporting_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
uint8_t v_isExporting_boxed_922_; lean_object* v_res_923_; 
v_isExporting_boxed_922_ = lean_unbox(v_isExporting_916_);
v_res_923_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_915_, v_isExporting_boxed_922_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_924_, uint8_t v_when_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
if (v_when_925_ == 0)
{
lean_object* v___x_931_; 
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
v___x_931_ = lean_apply_5(v_x_924_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, lean_box(0));
return v___x_931_;
}
else
{
uint8_t v___x_932_; lean_object* v___x_933_; 
v___x_932_ = 0;
v___x_933_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_924_, v___x_932_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_934_, lean_object* v_when_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_when_boxed_941_; lean_object* v_res_942_; 
v_when_boxed_941_ = lean_unbox(v_when_935_);
v_res_942_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_934_, v_when_boxed_941_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_943_, lean_object* v_projDecls_944_, lean_object* v___x_945_, lean_object* v___x_946_, uint8_t v_instImplicit_947_, lean_object* v___x_948_, lean_object* v_params_949_, lean_object* v_self_950_, lean_object* v_a_951_, lean_object* v___x_952_, lean_object* v_n_953_, lean_object* v___x_954_, uint8_t v_a_955_, lean_object* v_a_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_lt(v_a_956_, v_upperBound_943_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v_a_956_);
lean_dec(v___x_954_);
lean_dec(v_n_953_);
lean_dec_ref(v___x_952_);
lean_dec_ref(v_a_951_);
lean_dec_ref(v_self_950_);
lean_dec_ref(v_params_949_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_b_957_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v_ref_966_; lean_object* v_projName_967_; lean_object* v_paramInfoOverrides_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___f_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___y_975_; uint8_t v___x_976_; lean_object* v___x_977_; 
v___x_965_ = lean_array_fget_borrowed(v_projDecls_944_, v_a_956_);
v_ref_966_ = lean_ctor_get(v___x_965_, 0);
v_projName_967_ = lean_ctor_get(v___x_965_, 1);
v_paramInfoOverrides_968_ = lean_ctor_get(v___x_965_, 2);
v___x_969_ = lean_box(v_instImplicit_947_);
v___x_970_ = lean_box(v___x_963_);
v___x_971_ = lean_box(v_a_955_);
lean_inc(v___x_954_);
lean_inc_n(v_ref_966_, 2);
lean_inc_n(v_n_953_, 2);
lean_inc(v_paramInfoOverrides_968_);
lean_inc_ref(v___x_952_);
lean_inc_ref(v_a_951_);
lean_inc_ref(v_b_957_);
lean_inc_ref(v_self_950_);
lean_inc_ref(v_params_949_);
lean_inc(v___x_948_);
lean_inc(v_a_956_);
lean_inc(v___x_946_);
lean_inc_n(v_projName_967_, 2);
lean_inc_ref(v___x_945_);
v___f_972_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_972_, 0, v___x_945_);
lean_closure_set(v___f_972_, 1, v_projName_967_);
lean_closure_set(v___f_972_, 2, v___x_946_);
lean_closure_set(v___f_972_, 3, v_a_956_);
lean_closure_set(v___f_972_, 4, v___x_969_);
lean_closure_set(v___f_972_, 5, v___x_948_);
lean_closure_set(v___f_972_, 6, v_params_949_);
lean_closure_set(v___f_972_, 7, v_self_950_);
lean_closure_set(v___f_972_, 8, v_b_957_);
lean_closure_set(v___f_972_, 9, v___x_970_);
lean_closure_set(v___f_972_, 10, v_a_951_);
lean_closure_set(v___f_972_, 11, v___x_952_);
lean_closure_set(v___f_972_, 12, v_paramInfoOverrides_968_);
lean_closure_set(v___f_972_, 13, v_n_953_);
lean_closure_set(v___f_972_, 14, v_ref_966_);
lean_closure_set(v___f_972_, 15, v___x_954_);
lean_closure_set(v___f_972_, 16, v___x_971_);
v___x_973_ = l_Lean_Expr_isForall(v_b_957_);
lean_dec_ref(v_b_957_);
v___x_974_ = lean_box(v___x_973_);
v___y_975_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_975_, 0, v___x_974_);
lean_closure_set(v___y_975_, 1, v_projName_967_);
lean_closure_set(v___y_975_, 2, v_n_953_);
lean_closure_set(v___y_975_, 3, v_ref_966_);
lean_closure_set(v___y_975_, 4, v___f_972_);
v___x_976_ = l_Lean_isPrivateName(v_projName_967_);
v___x_977_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_975_, v___x_976_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_add(v_a_956_, v___x_979_);
lean_dec(v_a_956_);
v_a_956_ = v___x_980_;
v_b_957_ = v_a_978_;
goto _start;
}
else
{
lean_dec(v_a_956_);
lean_dec(v___x_954_);
lean_dec(v_n_953_);
lean_dec_ref(v___x_952_);
lean_dec_ref(v_a_951_);
lean_dec_ref(v_self_950_);
lean_dec_ref(v_params_949_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
lean_dec_ref(v___x_945_);
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_982_ = _args[0];
lean_object* v_projDecls_983_ = _args[1];
lean_object* v___x_984_ = _args[2];
lean_object* v___x_985_ = _args[3];
lean_object* v_instImplicit_986_ = _args[4];
lean_object* v___x_987_ = _args[5];
lean_object* v_params_988_ = _args[6];
lean_object* v_self_989_ = _args[7];
lean_object* v_a_990_ = _args[8];
lean_object* v___x_991_ = _args[9];
lean_object* v_n_992_ = _args[10];
lean_object* v___x_993_ = _args[11];
lean_object* v_a_994_ = _args[12];
lean_object* v_a_995_ = _args[13];
lean_object* v_b_996_ = _args[14];
lean_object* v___y_997_ = _args[15];
lean_object* v___y_998_ = _args[16];
lean_object* v___y_999_ = _args[17];
lean_object* v___y_1000_ = _args[18];
lean_object* v___y_1001_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1002_; uint8_t v_a_19538__boxed_1003_; lean_object* v_res_1004_; 
v_instImplicit_boxed_1002_ = lean_unbox(v_instImplicit_986_);
v_a_19538__boxed_1003_ = lean_unbox(v_a_994_);
v_res_1004_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_982_, v_projDecls_983_, v___x_984_, v___x_985_, v_instImplicit_boxed_1002_, v___x_987_, v_params_988_, v_self_989_, v_a_990_, v___x_991_, v_n_992_, v___x_993_, v_a_19538__boxed_1003_, v_a_995_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec_ref(v_projDecls_983_);
lean_dec(v_upperBound_982_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1005_, lean_object* v_as_1006_, size_t v_sz_1007_, size_t v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_usize_dec_lt(v_i_1008_, v_sz_1007_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_b_1009_);
return v___x_1015_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_array_uget_borrowed(v_as_1006_, v_i_1008_);
v___x_1017_ = l_Lean_Expr_fvarId_x21(v_a_1016_);
lean_inc(v___x_1017_);
v___x_1018_ = l_Lean_FVarId_getDecl___redArg(v___x_1017_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_a_1021_; uint8_t v___y_1026_; uint8_t v___x_1029_; uint8_t v___x_1030_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1029_ = l_Lean_LocalDecl_binderInfo(v_a_1019_);
v___x_1030_ = l_Lean_BinderInfo_isInstImplicit(v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = l_Lean_LocalDecl_type(v_a_1019_);
lean_dec(v_a_1019_);
v___x_1033_ = l_Lean_Expr_isOutParam(v___x_1032_);
lean_dec_ref(v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = 0;
v___x_1035_ = l_Lean_LocalContext_setBinderInfo(v_b_1009_, v___x_1017_, v___x_1034_);
v_a_1021_ = v___x_1035_;
goto v___jp_1020_;
}
else
{
goto v___jp_1031_;
}
}
else
{
lean_dec(v_a_1019_);
goto v___jp_1031_;
}
v___jp_1020_:
{
size_t v___x_1022_; size_t v___x_1023_; 
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1008_, v___x_1022_);
v_i_1008_ = v___x_1023_;
v_b_1009_ = v_a_1021_;
goto _start;
}
v___jp_1025_:
{
if (v___y_1026_ == 0)
{
lean_dec(v___x_1017_);
v_a_1021_ = v_b_1009_;
goto v___jp_1020_;
}
else
{
uint8_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = 1;
v___x_1028_ = l_Lean_LocalContext_setBinderInfo(v_b_1009_, v___x_1017_, v___x_1027_);
v_a_1021_ = v___x_1028_;
goto v___jp_1020_;
}
}
v___jp_1031_:
{
if (v___x_1030_ == 0)
{
v___y_1026_ = v___x_1030_;
goto v___jp_1025_;
}
else
{
v___y_1026_ = v_instImplicit_1005_;
goto v___jp_1025_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v___x_1017_);
lean_dec_ref(v_b_1009_);
v_a_1036_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1018_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1018_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1044_, lean_object* v_as_1045_, lean_object* v_sz_1046_, lean_object* v_i_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
uint8_t v_instImplicit_boxed_1053_; size_t v_sz_boxed_1054_; size_t v_i_boxed_1055_; lean_object* v_res_1056_; 
v_instImplicit_boxed_1053_ = lean_unbox(v_instImplicit_1044_);
v_sz_boxed_1054_ = lean_unbox_usize(v_sz_1046_);
lean_dec(v_sz_1046_);
v_i_boxed_1055_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1053_, v_as_1045_, v_sz_boxed_1054_, v_i_boxed_1055_, v_b_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec_ref(v_as_1045_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1057_, uint8_t v_instImplicit_1058_, lean_object* v_projDecls_1059_, lean_object* v_toConstantVal_1060_, lean_object* v_numParams_1061_, lean_object* v___x_1062_, lean_object* v_n_1063_, lean_object* v_levelParams_1064_, uint8_t v_a_1065_, lean_object* v_ctorType_1066_, lean_object* v_self_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_lctx_1073_; lean_object* v___x_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v_lctx_1073_ = lean_ctor_get(v___y_1068_, 2);
lean_inc_ref(v_self_1067_);
lean_inc_ref(v_params_1057_);
v___x_1074_ = lean_array_push(v_params_1057_, v_self_1067_);
v_sz_1075_ = lean_array_size(v_params_1057_);
v___x_1076_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1073_);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1058_, v_params_1057_, v_sz_1075_, v___x_1076_, v_lctx_1073_, v___y_1068_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = lean_array_get_size(v_projDecls_1059_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1079_, v_projDecls_1059_, v_toConstantVal_1060_, v_numParams_1061_, v_instImplicit_1058_, v___x_1062_, v_params_1057_, v_self_1067_, v_a_1078_, v___x_1074_, v_n_1063_, v_levelParams_1064_, v_a_1065_, v___x_1080_, v_ctorType_1066_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1081_, 0);
lean_dec(v_unused_1090_);
v___x_1083_ = v___x_1081_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v___x_1081_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1081_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1081_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v___x_1074_);
lean_dec_ref(v_self_1067_);
lean_dec_ref(v_ctorType_1066_);
lean_dec(v_levelParams_1064_);
lean_dec(v_n_1063_);
lean_dec(v___x_1062_);
lean_dec(v_numParams_1061_);
lean_dec_ref(v_toConstantVal_1060_);
lean_dec_ref(v_params_1057_);
v_a_1099_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1077_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1077_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1107_, lean_object* v_instImplicit_1108_, lean_object* v_projDecls_1109_, lean_object* v_toConstantVal_1110_, lean_object* v_numParams_1111_, lean_object* v___x_1112_, lean_object* v_n_1113_, lean_object* v_levelParams_1114_, lean_object* v_a_1115_, lean_object* v_ctorType_1116_, lean_object* v_self_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_instImplicit_boxed_1123_; uint8_t v_a_19680__boxed_1124_; lean_object* v_res_1125_; 
v_instImplicit_boxed_1123_ = lean_unbox(v_instImplicit_1108_);
v_a_19680__boxed_1124_ = lean_unbox(v_a_1115_);
v_res_1125_ = l_Lean_Meta_mkProjections___lam__0(v_params_1107_, v_instImplicit_boxed_1123_, v_projDecls_1109_, v_toConstantVal_1110_, v_numParams_1111_, v___x_1112_, v_n_1113_, v_levelParams_1114_, v_a_19680__boxed_1124_, v_ctorType_1116_, v_self_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_projDecls_1109_);
return v_res_1125_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1131_ = l_Lean_stringToMessageData(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1135_, lean_object* v_projDecls_1136_, lean_object* v_toConstantVal_1137_, lean_object* v_numParams_1138_, lean_object* v___x_1139_, lean_object* v_n_1140_, lean_object* v_levelParams_1141_, uint8_t v_a_1142_, lean_object* v_params_1143_, lean_object* v_ctorType_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1161_ = lean_box(v_instImplicit_1135_);
v___x_1162_ = lean_box(v_a_1142_);
lean_inc(v_n_1140_);
lean_inc(v___x_1139_);
lean_inc(v_numParams_1138_);
lean_inc_ref(v_params_1143_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1163_, 0, v_params_1143_);
lean_closure_set(v___f_1163_, 1, v___x_1161_);
lean_closure_set(v___f_1163_, 2, v_projDecls_1136_);
lean_closure_set(v___f_1163_, 3, v_toConstantVal_1137_);
lean_closure_set(v___f_1163_, 4, v_numParams_1138_);
lean_closure_set(v___f_1163_, 5, v___x_1139_);
lean_closure_set(v___f_1163_, 6, v_n_1140_);
lean_closure_set(v___f_1163_, 7, v_levelParams_1141_);
lean_closure_set(v___f_1163_, 8, v___x_1162_);
lean_closure_set(v___f_1163_, 9, v_ctorType_1144_);
v___x_1169_ = lean_array_get_size(v_params_1143_);
v___x_1170_ = lean_nat_dec_eq(v___x_1169_, v_numParams_1138_);
lean_dec(v_numParams_1138_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v___f_1163_);
lean_dec_ref(v_params_1143_);
lean_dec(v___x_1139_);
v___x_1171_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1172_ = l_Lean_MessageData_ofConstName(v_n_1140_, v___x_1170_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1175_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1176_;
}
else
{
goto v___jp_1164_;
}
v___jp_1150_:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1159_ = 0;
v___x_1160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1158_, v___y_1157_, v___y_1153_, v___y_1156_, v___x_1159_, v___y_1152_, v___y_1155_, v___y_1154_, v___y_1151_);
return v___x_1160_;
}
v___jp_1164_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = l_Lean_Expr_const___override(v_n_1140_, v___x_1139_);
v___x_1166_ = l_Lean_mkAppN(v___x_1165_, v_params_1143_);
lean_dec_ref(v_params_1143_);
if (v_instImplicit_1135_ == 0)
{
uint8_t v___x_1167_; 
v___x_1167_ = 0;
v___y_1151_ = v___y_1148_;
v___y_1152_ = v___y_1145_;
v___y_1153_ = v___x_1166_;
v___y_1154_ = v___y_1147_;
v___y_1155_ = v___y_1146_;
v___y_1156_ = v___f_1163_;
v___y_1157_ = v___x_1167_;
goto v___jp_1150_;
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = 3;
v___y_1151_ = v___y_1148_;
v___y_1152_ = v___y_1145_;
v___y_1153_ = v___x_1166_;
v___y_1154_ = v___y_1147_;
v___y_1155_ = v___y_1146_;
v___y_1156_ = v___f_1163_;
v___y_1157_ = v___x_1168_;
goto v___jp_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1177_, lean_object* v_projDecls_1178_, lean_object* v_toConstantVal_1179_, lean_object* v_numParams_1180_, lean_object* v___x_1181_, lean_object* v_n_1182_, lean_object* v_levelParams_1183_, lean_object* v_a_1184_, lean_object* v_params_1185_, lean_object* v_ctorType_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_instImplicit_boxed_1192_; uint8_t v_a_19784__boxed_1193_; lean_object* v_res_1194_; 
v_instImplicit_boxed_1192_ = lean_unbox(v_instImplicit_1177_);
v_a_19784__boxed_1193_ = lean_unbox(v_a_1184_);
v_res_1194_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1192_, v_projDecls_1178_, v_toConstantVal_1179_, v_numParams_1180_, v___x_1181_, v_n_1182_, v_levelParams_1183_, v_a_19784__boxed_1193_, v_params_1185_, v_ctorType_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
if (lean_obj_tag(v_a_1195_) == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = l_List_reverse___redArg(v_a_1196_);
return v___x_1197_;
}
else
{
lean_object* v_head_1198_; lean_object* v_tail_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_head_1198_ = lean_ctor_get(v_a_1195_, 0);
v_tail_1199_ = lean_ctor_get(v_a_1195_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v_a_1195_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_tail_1199_);
lean_inc(v_head_1198_);
lean_dec(v_a_1195_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = l_Lean_mkLevelParam(v_head_1198_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v_a_1196_);
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1196_);
v___x_1205_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
v_a_1195_ = v_tail_1199_;
v_a_1196_ = v___x_1205_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_instMonadEIO(lean_box(0));
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_toApplicative_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1283_; 
v___x_1220_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1221_ = l_StateRefT_x27_instMonad___redArg(v___x_1220_);
v_toApplicative_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1221_, 1);
lean_dec(v_unused_1284_);
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1283_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_toApplicative_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1283_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_toFunctor_1226_; lean_object* v_toSeq_1227_; lean_object* v_toSeqLeft_1228_; lean_object* v_toSeqRight_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1281_; 
v_toFunctor_1226_ = lean_ctor_get(v_toApplicative_1222_, 0);
v_toSeq_1227_ = lean_ctor_get(v_toApplicative_1222_, 2);
v_toSeqLeft_1228_ = lean_ctor_get(v_toApplicative_1222_, 3);
v_toSeqRight_1229_ = lean_ctor_get(v_toApplicative_1222_, 4);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_toApplicative_1222_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_toApplicative_1222_, 1);
lean_dec(v_unused_1282_);
v___x_1231_ = v_toApplicative_1222_;
v_isShared_1232_ = v_isSharedCheck_1281_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_toSeqRight_1229_);
lean_inc(v_toSeqLeft_1228_);
lean_inc(v_toSeq_1227_);
lean_inc(v_toFunctor_1226_);
lean_dec(v_toApplicative_1222_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1281_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1242_; 
v___f_1233_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1234_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1226_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toFunctor_1226_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1226_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___f_1235_);
lean_ctor_set(v___x_1237_, 1, v___f_1236_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toSeqRight_1229_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toSeqLeft_1228_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeq_1227_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___f_1238_);
lean_ctor_set(v___x_1231_, 3, v___f_1239_);
lean_ctor_set(v___x_1231_, 2, v___f_1240_);
lean_ctor_set(v___x_1231_, 1, v___f_1233_);
lean_ctor_set(v___x_1231_, 0, v___x_1237_);
v___x_1242_ = v___x_1231_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___f_1233_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v___f_1240_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v___f_1239_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v___f_1238_);
v___x_1242_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___f_1234_);
lean_ctor_set(v___x_1224_, 0, v___x_1242_);
v___x_1244_ = v___x_1224_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___f_1234_);
v___x_1244_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v_toApplicative_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1277_; 
v___x_1245_ = l_StateRefT_x27_instMonad___redArg(v___x_1244_);
v_toApplicative_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1245_, 1);
lean_dec(v_unused_1278_);
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1277_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_toApplicative_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1277_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_toFunctor_1250_; lean_object* v_toSeq_1251_; lean_object* v_toSeqLeft_1252_; lean_object* v_toSeqRight_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1275_; 
v_toFunctor_1250_ = lean_ctor_get(v_toApplicative_1246_, 0);
v_toSeq_1251_ = lean_ctor_get(v_toApplicative_1246_, 2);
v_toSeqLeft_1252_ = lean_ctor_get(v_toApplicative_1246_, 3);
v_toSeqRight_1253_ = lean_ctor_get(v_toApplicative_1246_, 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_toApplicative_1246_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_toApplicative_1246_, 1);
lean_dec(v_unused_1276_);
v___x_1255_ = v_toApplicative_1246_;
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_toSeqRight_1253_);
lean_inc(v_toSeqLeft_1252_);
lean_inc(v_toSeq_1251_);
lean_inc(v_toFunctor_1250_);
lean_dec(v_toApplicative_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1275_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1266_; 
v___f_1257_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1258_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1250_);
v___f_1259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1259_, 0, v_toFunctor_1250_);
v___f_1260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1260_, 0, v_toFunctor_1250_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___f_1259_);
lean_ctor_set(v___x_1261_, 1, v___f_1260_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeqRight_1253_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeqLeft_1252_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toSeq_1251_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 4, v___f_1262_);
lean_ctor_set(v___x_1255_, 3, v___f_1263_);
lean_ctor_set(v___x_1255_, 2, v___f_1264_);
lean_ctor_set(v___x_1255_, 1, v___f_1257_);
lean_ctor_set(v___x_1255_, 0, v___x_1261_);
v___x_1266_ = v___x_1255_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___f_1264_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___f_1262_);
v___x_1266_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___f_1258_);
lean_ctor_set(v___x_1248_, 0, v___x_1266_);
v___x_1268_ = v___x_1248_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___f_1258_);
v___x_1268_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_14621__overap_1271_; lean_object* v___x_1272_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_instInhabitedOfMonad___redArg(v___x_1268_, v___x_1269_);
v___x_14621__overap_1271_ = lean_panic_fn_borrowed(v___x_1270_, v_msg_1214_);
lean_dec(v___x_1270_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
v___x_1272_ = lean_apply_5(v___x_14621__overap_1271_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1272_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1291_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1299_ = lean_unsigned_to_nat(11u);
v___x_1300_ = lean_unsigned_to_nat(122u);
v___x_1301_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1302_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1303_ = l_mkPanicMessageWithDecl(v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_, v___x_1298_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1318_; lean_object* v_env_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_st_ref_get(v___y_1308_);
v_env_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = 0;
lean_inc(v_constName_1304_);
v___x_1321_ = l_Lean_Environment_findAsync_x3f(v_env_1319_, v_constName_1304_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 1)
{
lean_object* v_val_1322_; uint8_t v_kind_1323_; 
v_val_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v_kind_1323_ = lean_ctor_get_uint8(v_val_1322_, sizeof(void*)*3);
if (v_kind_1323_ == 6)
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1322_);
if (lean_obj_tag(v___x_1324_) == 6)
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_constName_1304_);
v_val_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_val_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___x_1324_);
v___x_1333_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1334_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1333_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
if (lean_obj_tag(v_a_1335_) == 0)
{
lean_del_object(v___x_1337_);
goto v___jp_1310_;
}
else
{
lean_object* v_val_1339_; lean_object* v___x_1341_; 
lean_dec(v_constName_1304_);
v_val_1339_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_a_1335_, 1);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_val_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_val_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_constName_1304_);
v_a_1344_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1334_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1334_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
else
{
lean_dec(v_val_1322_);
goto v___jp_1310_;
}
}
else
{
lean_dec(v___x_1321_);
goto v___jp_1310_;
}
v___jp_1310_:
{
lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1312_ = 0;
v___x_1313_ = l_Lean_MessageData_ofConstName(v_constName_1304_, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1311_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1316_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
return v___x_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v_env_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_st_ref_get(v___y_1366_);
v_env_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref(v_env_1369_);
lean_dec(v___x_1368_);
lean_inc(v_constName_1362_);
v___x_1370_ = l_Lean_isInductiveCore_x3f(v_env_1369_, v_constName_1362_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1371_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1372_ = 0;
v___x_1373_ = l_Lean_MessageData_ofConstName(v_constName_1362_, v___x_1372_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1371_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1376_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_constName_1362_);
v_val_1378_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1370_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_val_1378_);
lean_dec(v___x_1370_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 0);
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1392_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1399_, lean_object* v___x_1400_, uint8_t v_instImplicit_1401_, lean_object* v_projDecls_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
lean_inc(v_n_1399_);
v___x_1408_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1399_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1450_ = l_Lean_InductiveVal_numCtors(v_a_1409_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_dec_eq(v___x_1450_, v___x_1451_);
lean_dec(v___x_1450_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_a_1409_);
lean_dec_ref(v_projDecls_1402_);
v___x_1453_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1454_ = l_Lean_MessageData_ofConstName(v_n_1399_, v___x_1452_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1457_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1458_;
}
else
{
v___y_1411_ = v___y_1403_;
v___y_1412_ = v___y_1404_;
v___y_1413_ = v___y_1405_;
v___y_1414_ = v___y_1406_;
goto v___jp_1410_;
}
v___jp_1410_:
{
lean_object* v_toConstantVal_1415_; lean_object* v_numParams_1416_; lean_object* v_ctors_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_toConstantVal_1415_ = lean_ctor_get(v_a_1409_, 0);
lean_inc_ref(v_toConstantVal_1415_);
v_numParams_1416_ = lean_ctor_get(v_a_1409_, 1);
lean_inc(v_numParams_1416_);
v_ctors_1417_ = lean_ctor_get(v_a_1409_, 4);
lean_inc(v_ctors_1417_);
lean_dec(v_a_1409_);
v___x_1418_ = l_List_head_x21___redArg(v___x_1400_, v_ctors_1417_);
lean_dec(v_ctors_1417_);
v___x_1419_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1418_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_levelParams_1421_; lean_object* v_type_1422_; lean_object* v___x_1423_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v_levelParams_1421_ = lean_ctor_get(v_toConstantVal_1415_, 1);
lean_inc(v_levelParams_1421_);
v_type_1422_ = lean_ctor_get(v_toConstantVal_1415_, 2);
lean_inc_ref(v_type_1422_);
lean_dec_ref(v_toConstantVal_1415_);
v___x_1423_ = l_Lean_Meta_isPropFormerType(v_type_1422_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_toConstantVal_1424_; lean_object* v_a_1425_; lean_object* v_type_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v_toConstantVal_1424_ = lean_ctor_get(v_a_1420_, 0);
lean_inc_ref(v_toConstantVal_1424_);
lean_dec(v_a_1420_);
v_a_1425_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1423_, 1);
v_type_1426_ = lean_ctor_get(v_toConstantVal_1424_, 2);
lean_inc_ref(v_type_1426_);
v___x_1427_ = lean_box(0);
lean_inc(v_levelParams_1421_);
v___x_1428_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1421_, v___x_1427_);
v___x_1429_ = lean_box(v_instImplicit_1401_);
lean_inc(v_numParams_1416_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1430_, 0, v___x_1429_);
lean_closure_set(v___f_1430_, 1, v_projDecls_1402_);
lean_closure_set(v___f_1430_, 2, v_toConstantVal_1424_);
lean_closure_set(v___f_1430_, 3, v_numParams_1416_);
lean_closure_set(v___f_1430_, 4, v___x_1428_);
lean_closure_set(v___f_1430_, 5, v_n_1399_);
lean_closure_set(v___f_1430_, 6, v_levelParams_1421_);
lean_closure_set(v___f_1430_, 7, v_a_1425_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_numParams_1416_);
v___x_1432_ = 0;
v___x_1433_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1426_, v___x_1431_, v___f_1430_, v___x_1432_, v___x_1432_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1433_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_levelParams_1421_);
lean_dec(v_a_1420_);
lean_dec(v_numParams_1416_);
lean_dec_ref(v_projDecls_1402_);
lean_dec(v_n_1399_);
v_a_1434_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1423_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1423_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_numParams_1416_);
lean_dec_ref(v_toConstantVal_1415_);
lean_dec_ref(v_projDecls_1402_);
lean_dec(v_n_1399_);
v_a_1442_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1419_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1419_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v_projDecls_1402_);
lean_dec(v_n_1399_);
v_a_1459_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1408_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1408_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1467_, lean_object* v___x_1468_, lean_object* v_instImplicit_1469_, lean_object* v_projDecls_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v_instImplicit_boxed_1476_; lean_object* v_res_1477_; 
v_instImplicit_boxed_1476_ = lean_unbox(v_instImplicit_1469_);
v_res_1477_ = l_Lean_Meta_mkProjections___lam__2(v_n_1467_, v___x_1468_, v_instImplicit_boxed_1476_, v_projDecls_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___x_1468_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_unsigned_to_nat(32u);
v___x_1482_ = lean_mk_empty_array_with_capacity(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1484_ = ((size_t)5ULL);
v___x_1485_ = lean_unsigned_to_nat(0u);
v___x_1486_ = lean_unsigned_to_nat(32u);
v___x_1487_ = lean_mk_empty_array_with_capacity(v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1489_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
lean_ctor_set(v___x_1489_, 2, v___x_1485_);
lean_ctor_set(v___x_1489_, 3, v___x_1485_);
lean_ctor_set_usize(v___x_1489_, 4, v___x_1484_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1490_ = lean_box(1);
v___x_1491_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1492_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v___x_1491_);
lean_ctor_set(v___x_1493_, 2, v___x_1490_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1496_, lean_object* v_projDecls_1497_, uint8_t v_instImplicit_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_box(v_instImplicit_1498_);
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1506_, 0, v_n_1496_);
lean_closure_set(v___f_1506_, 1, v___x_1504_);
lean_closure_set(v___f_1506_, 2, v___x_1505_);
lean_closure_set(v___f_1506_, 3, v_projDecls_1497_);
v___x_1507_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1508_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1509_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1507_, v___x_1508_, v___f_1506_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1510_, lean_object* v_projDecls_1511_, lean_object* v_instImplicit_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
uint8_t v_instImplicit_boxed_1518_; lean_object* v_res_1519_; 
v_instImplicit_boxed_1518_ = lean_unbox(v_instImplicit_1512_);
v_res_1519_ = l_Lean_Meta_mkProjections(v_n_1510_, v_projDecls_1511_, v_instImplicit_boxed_1518_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1520_, lean_object* v_as_1521_, size_t v_sz_1522_, size_t v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1520_, v_as_1521_, v_sz_1522_, v_i_1523_, v_b_1524_, v___y_1525_, v___y_1527_, v___y_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1531_, lean_object* v_as_1532_, lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_instImplicit_boxed_1541_; size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_instImplicit_boxed_1541_ = lean_unbox(v_instImplicit_1531_);
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1541_, v_as_1532_, v_sz_boxed_1542_, v_i_boxed_1543_, v_b_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_as_1532_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1545_, uint8_t v_s_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1545_, v_s_1546_, v___y_1548_, v___y_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1553_, lean_object* v_s_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_s_boxed_1560_; lean_object* v_res_1561_; 
v_s_boxed_1560_ = lean_unbox(v_s_1554_);
v_res_1561_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1553_, v_s_boxed_1560_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1562_, lean_object* v_ref_1563_, lean_object* v_msg_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1563_, v_msg_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_ref_1572_, lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1571_, v_ref_1572_, v_msg_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v_ref_1572_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1580_, lean_object* v_x_1581_, uint8_t v_isExporting_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1581_, v_isExporting_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1589_, lean_object* v_x_1590_, lean_object* v_isExporting_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v_isExporting_boxed_1597_; lean_object* v_res_1598_; 
v_isExporting_boxed_1597_ = lean_unbox(v_isExporting_1591_);
v_res_1598_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1589_, v_x_1590_, v_isExporting_boxed_1597_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1599_, lean_object* v_x_1600_, uint8_t v_when_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1600_, v_when_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1608_, lean_object* v_x_1609_, lean_object* v_when_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v_when_boxed_1616_; lean_object* v_res_1617_; 
v_when_boxed_1616_ = lean_unbox(v_when_1610_);
v_res_1617_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1608_, v_x_1609_, v_when_boxed_1616_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1618_, lean_object* v_projDecls_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, uint8_t v_instImplicit_1622_, lean_object* v___x_1623_, lean_object* v_params_1624_, lean_object* v_self_1625_, lean_object* v_a_1626_, lean_object* v___x_1627_, lean_object* v_n_1628_, lean_object* v___x_1629_, uint8_t v_a_1630_, lean_object* v_inst_1631_, lean_object* v_R_1632_, lean_object* v_a_1633_, lean_object* v_b_1634_, lean_object* v_c_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1618_, v_projDecls_1619_, v___x_1620_, v___x_1621_, v_instImplicit_1622_, v___x_1623_, v_params_1624_, v_self_1625_, v_a_1626_, v___x_1627_, v_n_1628_, v___x_1629_, v_a_1630_, v_a_1633_, v_b_1634_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1642_ = _args[0];
lean_object* v_projDecls_1643_ = _args[1];
lean_object* v___x_1644_ = _args[2];
lean_object* v___x_1645_ = _args[3];
lean_object* v_instImplicit_1646_ = _args[4];
lean_object* v___x_1647_ = _args[5];
lean_object* v_params_1648_ = _args[6];
lean_object* v_self_1649_ = _args[7];
lean_object* v_a_1650_ = _args[8];
lean_object* v___x_1651_ = _args[9];
lean_object* v_n_1652_ = _args[10];
lean_object* v___x_1653_ = _args[11];
lean_object* v_a_1654_ = _args[12];
lean_object* v_inst_1655_ = _args[13];
lean_object* v_R_1656_ = _args[14];
lean_object* v_a_1657_ = _args[15];
lean_object* v_b_1658_ = _args[16];
lean_object* v_c_1659_ = _args[17];
lean_object* v___y_1660_ = _args[18];
lean_object* v___y_1661_ = _args[19];
lean_object* v___y_1662_ = _args[20];
lean_object* v___y_1663_ = _args[21];
lean_object* v___y_1664_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1665_; uint8_t v_a_20537__boxed_1666_; lean_object* v_res_1667_; 
v_instImplicit_boxed_1665_ = lean_unbox(v_instImplicit_1646_);
v_a_20537__boxed_1666_ = lean_unbox(v_a_1654_);
v_res_1667_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1642_, v_projDecls_1643_, v___x_1644_, v___x_1645_, v_instImplicit_boxed_1665_, v___x_1647_, v_params_1648_, v_self_1649_, v_a_1650_, v___x_1651_, v_n_1652_, v___x_1653_, v_a_20537__boxed_1666_, v_inst_1655_, v_R_1656_, v_a_1657_, v_b_1658_, v_c_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec_ref(v_projDecls_1643_);
lean_dec(v_upperBound_1642_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1668_, uint8_t v_allowLevelAssignments_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1669_, v_k_1668_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
v_a_1684_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1675_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1675_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1692_, lean_object* v_allowLevelAssignments_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1699_; lean_object* v_res_1700_; 
v_allowLevelAssignments_boxed_1699_ = lean_unbox(v_allowLevelAssignments_1693_);
v_res_1700_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1692_, v_allowLevelAssignments_boxed_1699_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1701_, lean_object* v_k_1702_, uint8_t v_allowLevelAssignments_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1702_, v_allowLevelAssignments_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1710_, lean_object* v_k_1711_, lean_object* v_allowLevelAssignments_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1718_; lean_object* v_res_1719_; 
v_allowLevelAssignments_boxed_1718_ = lean_unbox(v_allowLevelAssignments_1712_);
v_res_1719_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1710_, v_k_1711_, v_allowLevelAssignments_boxed_1718_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1720_, size_t v_sz_1721_, size_t v_i_1722_, lean_object* v_b_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_usize_dec_lt(v_i_1722_, v_sz_1721_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_b_1723_);
return v___x_1730_;
}
else
{
lean_object* v_snd_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1786_; 
v_snd_1731_ = lean_ctor_get(v_b_1723_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_b_1723_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_b_1723_, 0);
lean_dec(v_unused_1787_);
v___x_1733_ = v_b_1723_;
v_isShared_1734_ = v_isSharedCheck_1786_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_snd_1731_);
lean_dec(v_b_1723_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1786_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_array_1735_; lean_object* v_start_1736_; lean_object* v_stop_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_array_1735_ = lean_ctor_get(v_snd_1731_, 0);
v_start_1736_ = lean_ctor_get(v_snd_1731_, 1);
v_stop_1737_ = lean_ctor_get(v_snd_1731_, 2);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_nat_dec_lt(v_start_1736_, v_stop_1737_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1741_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1738_);
v___x_1741_ = v___x_1733_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_snd_1731_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
else
{
lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1782_; 
lean_inc(v_stop_1737_);
lean_inc(v_start_1736_);
lean_inc_ref(v_array_1735_);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_snd_1731_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; lean_object* v_unused_1784_; lean_object* v_unused_1785_; 
v_unused_1783_ = lean_ctor_get(v_snd_1731_, 2);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v_snd_1731_, 1);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v_snd_1731_, 0);
lean_dec(v_unused_1785_);
v___x_1745_ = v_snd_1731_;
v_isShared_1746_ = v_isSharedCheck_1782_;
goto v_resetjp_1744_;
}
else
{
lean_dec(v_snd_1731_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1782_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_a_1747_ = lean_array_uget_borrowed(v_as_1720_, v_i_1722_);
v___x_1748_ = lean_array_fget_borrowed(v_array_1735_, v_start_1736_);
lean_inc(v___x_1748_);
lean_inc(v_a_1747_);
v___x_1749_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1747_, v___x_1748_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1773_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1773_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1773_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_add(v_start_1736_, v___x_1754_);
lean_dec(v_start_1736_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1755_);
v___x_1757_ = v___x_1745_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_array_1735_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_stop_1737_);
v___x_1757_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_unbox(v_a_1750_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_a_1750_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1757_);
lean_ctor_set(v___x_1733_, 0, v___x_1759_);
v___x_1761_ = v___x_1733_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1757_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1761_);
v___x_1763_ = v___x_1752_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v___x_1767_; 
lean_del_object(v___x_1752_);
lean_dec(v_a_1750_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1757_);
lean_ctor_set(v___x_1733_, 0, v___x_1738_);
v___x_1767_ = v___x_1733_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v___x_1757_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
size_t v___x_1768_; size_t v___x_1769_; 
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1722_, v___x_1768_);
v_i_1722_ = v___x_1769_;
v_b_1723_ = v___x_1767_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_del_object(v___x_1745_);
lean_dec(v_stop_1737_);
lean_dec(v_start_1736_);
lean_dec_ref(v_array_1735_);
lean_del_object(v___x_1733_);
v_a_1774_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1749_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1749_);
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
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1788_, lean_object* v_sz_1789_, lean_object* v_i_1790_, lean_object* v_b_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; lean_object* v_res_1799_; 
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1789_);
lean_dec(v_sz_1789_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1788_, v_sz_boxed_1797_, v_i_boxed_1798_, v_b_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec_ref(v_as_1788_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1800_, lean_object* v_params2_1801_, lean_object* v___x_1802_, lean_object* v_params1_1803_, uint8_t v___x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
if (v___x_1800_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v___x_1802_);
lean_dec_ref(v_params2_1801_);
v___x_1810_ = lean_box(v___x_1800_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; size_t v_sz_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l_Array_toSubarray___redArg(v_params2_1801_, v___x_1812_, v___x_1802_);
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1813_);
v_sz_1816_ = lean_array_size(v_params1_1803_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1803_, v_sz_1816_, v___x_1817_, v___x_1815_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1832_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1832_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_fst_1823_; 
v_fst_1823_ = lean_ctor_get(v_a_1819_, 0);
lean_inc(v_fst_1823_);
lean_dec(v_a_1819_);
if (lean_obj_tag(v_fst_1823_) == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_box(v___x_1804_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_object* v_val_1828_; lean_object* v___x_1830_; 
v_val_1828_ = lean_ctor_get(v_fst_1823_, 0);
lean_inc(v_val_1828_);
lean_dec_ref_known(v_fst_1823_, 1);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v_val_1828_);
v___x_1830_ = v___x_1821_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_val_1828_);
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
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1818_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1818_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1841_, lean_object* v_params2_1842_, lean_object* v___x_1843_, lean_object* v_params1_1844_, lean_object* v___x_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
uint8_t v___x_2097__boxed_1851_; uint8_t v___x_2099__boxed_1852_; lean_object* v_res_1853_; 
v___x_2097__boxed_1851_ = lean_unbox(v___x_1841_);
v___x_2099__boxed_1852_ = lean_unbox(v___x_1845_);
v_res_1853_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2097__boxed_1851_, v_params2_1842_, v___x_1843_, v_params1_1844_, v___x_2099__boxed_1852_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_params1_1844_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1854_, lean_object* v_params2_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___y_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1861_ = lean_array_get_size(v_params1_1854_);
v___x_1862_ = lean_array_get_size(v_params2_1855_);
v___x_1863_ = lean_nat_dec_eq(v___x_1861_, v___x_1862_);
v___x_1864_ = 1;
v___x_1865_ = lean_box(v___x_1863_);
v___x_1866_ = lean_box(v___x_1864_);
v___y_1867_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1867_, 0, v___x_1865_);
lean_closure_set(v___y_1867_, 1, v_params2_1855_);
lean_closure_set(v___y_1867_, 2, v___x_1862_);
lean_closure_set(v___y_1867_, 3, v_params1_1854_);
lean_closure_set(v___y_1867_, 4, v___x_1866_);
v___x_1868_ = 0;
v___x_1869_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1867_, v___x_1868_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1870_, lean_object* v_params2_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1870_, v_params2_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v_env_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_st_ref_get(v___y_1879_);
v_env_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_env_1882_);
lean_dec(v___x_1881_);
v___x_1883_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1882_, v_declName_1878_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1885_, v___y_1886_);
lean_dec(v___y_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1889_, v___y_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1903_; lean_object* v_dummy_1904_; 
v___x_1903_ = lean_box(0);
v_dummy_1904_ = l_Lean_Expr_sort___override(v___x_1903_);
return v_dummy_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1905_, lean_object* v_induct_1906_, lean_object* v_params_1907_, lean_object* v_idx_1908_, lean_object* v_e_1909_, lean_object* v_x_x3f_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
if (lean_obj_tag(v_e_1909_) == 11)
{
lean_object* v_typeName_1922_; lean_object* v_idx_1923_; lean_object* v_struct_1924_; uint8_t v___y_1972_; uint8_t v___x_1975_; 
v_typeName_1922_ = lean_ctor_get(v_e_1909_, 0);
v_idx_1923_ = lean_ctor_get(v_e_1909_, 1);
v_struct_1924_ = lean_ctor_get(v_e_1909_, 2);
lean_inc_ref(v_struct_1924_);
v___x_1975_ = lean_nat_dec_eq(v_idx_1923_, v_idx_1908_);
if (v___x_1975_ == 0)
{
v___y_1972_ = v___x_1975_;
goto v___jp_1971_;
}
else
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_name_eq(v_induct_1906_, v_typeName_1922_);
v___y_1972_ = v___x_1976_;
goto v___jp_1971_;
}
v___jp_1925_:
{
lean_object* v___x_1926_; 
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
v___x_1926_ = lean_infer_type(v_e_1909_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
lean_inc(v_a_1914_);
lean_inc_ref(v_a_1913_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
v___x_1928_ = lean_whnf(v_a_1927_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v_dummy_1930_; lean_object* v_nargs_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v_dummy_1930_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1931_ = l_Lean_Expr_getAppNumArgs(v_a_1929_);
lean_inc(v_nargs_1931_);
v___x_1932_ = lean_mk_array(v_nargs_1931_, v_dummy_1930_);
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = lean_nat_sub(v_nargs_1931_, v___x_1933_);
lean_dec(v_nargs_1931_);
v___x_1935_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1929_, v___x_1932_, v___x_1934_);
v___x_1936_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1907_, v___x_1935_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1946_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_unbox(v_a_1937_);
lean_dec(v_a_1937_);
if (v___x_1941_ == 0)
{
lean_del_object(v___x_1939_);
lean_dec_ref(v_struct_1924_);
goto v___jp_1916_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_struct_1924_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
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
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_struct_1924_);
v_a_1947_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1936_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1936_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_struct_1924_);
lean_dec_ref(v_params_1907_);
v_a_1955_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1928_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1928_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_struct_1924_);
lean_dec_ref(v_params_1907_);
v_a_1963_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1926_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1926_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1971_:
{
if (v___y_1972_ == 0)
{
lean_dec_ref(v_struct_1924_);
lean_dec_ref_known(v_e_1909_, 3);
lean_dec_ref(v_params_1907_);
goto v___jp_1916_;
}
else
{
if (lean_obj_tag(v_x_x3f_1910_) == 0)
{
goto v___jp_1925_;
}
else
{
lean_object* v_val_1973_; uint8_t v___x_1974_; 
v_val_1973_ = lean_ctor_get(v_x_x3f_1910_, 0);
v___x_1974_ = lean_expr_eqv(v_val_1973_, v_struct_1924_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_struct_1924_);
lean_dec_ref_known(v_e_1909_, 3);
lean_dec_ref(v_params_1907_);
goto v___jp_1916_;
}
else
{
goto v___jp_1925_;
}
}
}
}
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Expr_getAppFn(v_e_1909_);
if (lean_obj_tag(v___x_1977_) == 4)
{
lean_object* v_declName_1978_; lean_object* v___x_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2029_; 
v_declName_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_declName_1978_);
lean_dec_ref_known(v___x_1977_, 2);
v___x_1979_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1978_, v_a_1914_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2029_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2029_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___y_1985_; lean_object* v___y_1986_; 
if (lean_obj_tag(v_a_1980_) == 1)
{
lean_object* v_val_2014_; lean_object* v_ctorName_2015_; lean_object* v_numParams_2016_; lean_object* v_i_2017_; uint8_t v___y_2019_; uint8_t v___x_2027_; 
v_val_2014_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v_a_1980_, 1);
v_ctorName_2015_ = lean_ctor_get(v_val_2014_, 0);
lean_inc(v_ctorName_2015_);
v_numParams_2016_ = lean_ctor_get(v_val_2014_, 1);
lean_inc(v_numParams_2016_);
v_i_2017_ = lean_ctor_get(v_val_2014_, 2);
lean_inc(v_i_2017_);
lean_dec(v_val_2014_);
v___x_2027_ = lean_name_eq(v_ctorName_2015_, v_ctor_1905_);
lean_dec(v_ctorName_2015_);
if (v___x_2027_ == 0)
{
lean_dec(v_i_2017_);
v___y_2019_ = v___x_2027_;
goto v___jp_2018_;
}
else
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_eq(v_i_2017_, v_idx_1908_);
lean_dec(v_i_2017_);
v___y_2019_ = v___x_2028_;
goto v___jp_2018_;
}
v___jp_2018_:
{
if (v___y_2019_ == 0)
{
lean_dec(v_numParams_2016_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_e_1909_);
lean_dec_ref(v_params_1907_);
goto v___jp_1919_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2020_ = l_Lean_Expr_getAppNumArgs(v_e_1909_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v___x_2022_ = lean_nat_add(v_numParams_2016_, v___x_2021_);
lean_dec(v_numParams_2016_);
v___x_2023_ = lean_nat_dec_eq(v___x_2020_, v___x_2022_);
lean_dec(v___x_2022_);
lean_dec(v___x_2020_);
if (v___x_2023_ == 0)
{
lean_del_object(v___x_1982_);
lean_dec_ref(v_e_1909_);
lean_dec_ref(v_params_1907_);
goto v___jp_1919_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Expr_appArg_x21(v_e_1909_);
if (lean_obj_tag(v_x_x3f_1910_) == 0)
{
v___y_1985_ = v___x_2024_;
v___y_1986_ = v___x_2021_;
goto v___jp_1984_;
}
else
{
lean_object* v_val_2025_; uint8_t v___x_2026_; 
v_val_2025_ = lean_ctor_get(v_x_x3f_1910_, 0);
v___x_2026_ = lean_expr_eqv(v_val_2025_, v___x_2024_);
if (v___x_2026_ == 0)
{
lean_dec_ref(v___x_2024_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_e_1909_);
lean_dec_ref(v_params_1907_);
goto v___jp_1919_;
}
else
{
v___y_1985_ = v___x_2024_;
v___y_1986_ = v___x_2021_;
goto v___jp_1984_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1982_);
lean_dec(v_a_1980_);
lean_dec_ref(v_e_1909_);
lean_dec_ref(v_params_1907_);
goto v___jp_1919_;
}
v___jp_1984_:
{
lean_object* v___x_1987_; lean_object* v_dummy_1988_; lean_object* v_nargs_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = l_Lean_Expr_appFn_x21(v_e_1909_);
lean_dec_ref(v_e_1909_);
v_dummy_1988_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1989_ = l_Lean_Expr_getAppNumArgs(v___x_1987_);
lean_inc(v_nargs_1989_);
v___x_1990_ = lean_mk_array(v_nargs_1989_, v_dummy_1988_);
v___x_1991_ = lean_nat_sub(v_nargs_1989_, v___y_1986_);
lean_dec(v_nargs_1989_);
v___x_1992_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1987_, v___x_1990_, v___x_1991_);
v___x_1993_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1907_, v___x_1992_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2005_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2005_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_unbox(v_a_1994_);
lean_dec(v_a_1994_);
if (v___x_1998_ == 0)
{
lean_del_object(v___x_1996_);
lean_dec_ref(v___y_1985_);
lean_del_object(v___x_1982_);
goto v___jp_1919_;
}
else
{
lean_object* v___x_2000_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 1);
lean_ctor_set(v___x_1982_, 0, v___y_1985_);
v___x_2000_ = v___x_1982_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___y_1985_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2000_);
v___x_2002_ = v___x_1996_;
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
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v___y_1985_);
lean_del_object(v___x_1982_);
v_a_2006_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1993_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1993_);
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
}
}
else
{
lean_dec_ref(v___x_1977_);
lean_dec_ref(v_e_1909_);
lean_dec_ref(v_params_1907_);
goto v___jp_1919_;
}
}
v___jp_1916_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
return v___x_1918_;
}
v___jp_1919_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2030_, lean_object* v_induct_2031_, lean_object* v_params_2032_, lean_object* v_idx_2033_, lean_object* v_e_2034_, lean_object* v_x_x3f_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2030_, v_induct_2031_, v_params_2032_, v_idx_2033_, v_e_2034_, v_x_x3f_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_x_x3f_2035_);
lean_dec(v_idx_2033_);
lean_dec(v_induct_2031_);
lean_dec(v_ctor_2030_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v_env_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v___x_2048_ = lean_st_ref_get(v___y_2046_);
v_env_2052_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2048_);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_Environment_findAsync_x3f(v_env_2052_, v_constName_2042_, v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 1)
{
lean_object* v_val_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2074_; 
v_val_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2074_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_val_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2074_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
uint8_t v_kind_2059_; 
v_kind_2059_ = lean_ctor_get_uint8(v_val_2055_, sizeof(void*)*3);
if (v_kind_2059_ == 6)
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2055_);
if (lean_obj_tag(v___x_2060_) == 6)
{
lean_object* v_val_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2071_; 
v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_val_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_val_2061_);
v___x_2066_ = v___x_2057_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_val_2061_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2066_);
v___x_2068_ = v___x_2063_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v___x_2060_);
lean_del_object(v___x_2057_);
v___x_2072_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2073_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2072_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2073_;
}
}
else
{
lean_del_object(v___x_2057_);
lean_dec(v_val_2055_);
goto v___jp_2049_;
}
}
}
else
{
lean_dec(v___x_2054_);
goto v___jp_2049_;
}
v___jp_2049_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2090_, lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v_declName_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v_a_2096_, lean_object* v_val_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_nat_dec_lt(v_a_2098_, v_upperBound_2090_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec(v_a_2098_);
lean_dec_ref(v___x_2095_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_b_2099_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec_ref(v_b_2099_);
v___x_2107_ = l_Lean_instInhabitedExpr;
v___x_2108_ = lean_nat_add(v___x_2091_, v_a_2098_);
v___x_2109_ = lean_array_get_borrowed(v___x_2107_, v___x_2092_, v___x_2108_);
lean_dec(v___x_2108_);
lean_inc(v___x_2109_);
lean_inc_ref(v___x_2095_);
v___x_2110_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2093_, v___x_2094_, v___x_2095_, v_a_2098_, v___x_2109_, v_a_2096_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2129_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
if (lean_obj_tag(v_a_2111_) == 1)
{
lean_object* v_val_2115_; uint8_t v___x_2116_; 
v_val_2115_ = lean_ctor_get(v_a_2111_, 0);
lean_inc(v_val_2115_);
lean_dec_ref_known(v_a_2111_, 1);
v___x_2116_ = lean_expr_eqv(v_val_2115_, v_val_2097_);
lean_dec(v_val_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec(v_a_2098_);
lean_dec_ref(v___x_2095_);
v___x_2117_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2117_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_del_object(v___x_2113_);
v___x_2121_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_a_2098_, v___x_2122_);
lean_dec(v_a_2098_);
v_a_2098_ = v___x_2123_;
v_b_2099_ = v___x_2121_;
goto _start;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v_a_2111_);
lean_dec(v_a_2098_);
lean_dec_ref(v___x_2095_);
v___x_2125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2125_);
v___x_2127_ = v___x_2113_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
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
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2098_);
lean_dec_ref(v___x_2095_);
v_a_2130_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2110_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2110_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v_declName_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_a_2144_, lean_object* v_val_2145_, lean_object* v_a_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2138_, v___x_2139_, v___x_2140_, v_declName_2141_, v___x_2142_, v___x_2143_, v_a_2144_, v_val_2145_, v_a_2146_, v_b_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v_val_2145_);
lean_dec(v_a_2144_);
lean_dec(v___x_2142_);
lean_dec(v_declName_2141_);
lean_dec_ref(v___x_2140_);
lean_dec(v___x_2139_);
lean_dec(v_upperBound_2138_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2154_, lean_object* v_p_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_Expr_getAppFn(v_e_2154_);
if (lean_obj_tag(v___x_2161_) == 4)
{
lean_object* v_declName_2162_; lean_object* v___x_2163_; 
v_declName_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_n(v_declName_2162_, 2);
lean_dec_ref_known(v___x_2161_, 2);
v___x_2163_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2162_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2236_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2236_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2236_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
if (lean_obj_tag(v_a_2164_) == 1)
{
lean_object* v_val_2168_; lean_object* v_induct_2169_; lean_object* v_numParams_2170_; lean_object* v_numFields_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_val_2168_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v_a_2164_, 1);
v_induct_2169_ = lean_ctor_get(v_val_2168_, 1);
lean_inc_n(v_induct_2169_, 2);
v_numParams_2170_ = lean_ctor_get(v_val_2168_, 3);
lean_inc(v_numParams_2170_);
v_numFields_2171_ = lean_ctor_get(v_val_2168_, 4);
lean_inc(v_numFields_2171_);
lean_dec(v_val_2168_);
v___x_2172_ = lean_apply_1(v_p_2155_, v_induct_2169_);
v___x_2173_ = lean_unbox(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
lean_dec(v_numFields_2171_);
lean_dec(v_numParams_2170_);
lean_dec(v_induct_2169_);
lean_dec(v_declName_2162_);
lean_dec_ref(v_e_2154_);
v___x_2174_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2174_);
v___x_2176_ = v___x_2166_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___x_2178_; uint8_t v___y_2180_; uint8_t v___x_2228_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2228_ = lean_nat_dec_lt(v___x_2178_, v_numFields_2171_);
if (v___x_2228_ == 0)
{
v___y_2180_ = v___x_2228_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = l_Lean_Expr_getAppNumArgs(v_e_2154_);
v___x_2230_ = lean_nat_add(v_numParams_2170_, v_numFields_2171_);
v___x_2231_ = lean_nat_dec_eq(v___x_2229_, v___x_2230_);
lean_dec(v___x_2230_);
lean_dec(v___x_2229_);
v___y_2180_ = v___x_2231_;
goto v___jp_2179_;
}
v___jp_2179_:
{
if (v___y_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_numFields_2171_);
lean_dec(v_numParams_2170_);
lean_dec(v_induct_2169_);
lean_dec(v_declName_2162_);
lean_dec_ref(v_e_2154_);
v___x_2181_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2181_);
v___x_2183_ = v___x_2166_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
else
{
lean_object* v_dummy_2185_; lean_object* v_nargs_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_del_object(v___x_2166_);
v_dummy_2185_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2186_ = l_Lean_Expr_getAppNumArgs(v_e_2154_);
lean_inc(v_nargs_2186_);
v___x_2187_ = lean_mk_array(v_nargs_2186_, v_dummy_2185_);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_sub(v_nargs_2186_, v___x_2188_);
lean_dec(v_nargs_2186_);
v___x_2190_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2154_, v___x_2187_, v___x_2189_);
lean_inc(v_numParams_2170_);
v___x_2191_ = l_Array_extract___redArg(v___x_2190_, v___x_2178_, v_numParams_2170_);
v___x_2192_ = l_Lean_instInhabitedExpr;
v___x_2193_ = lean_array_get(v___x_2192_, v___x_2190_, v_numParams_2170_);
v___x_2194_ = lean_box(0);
lean_inc_ref(v___x_2191_);
v___x_2195_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2162_, v_induct_2169_, v___x_2191_, v___x_2178_, v___x_2193_, v___x_2194_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2227_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2227_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2227_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_val_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_del_object(v___x_2198_);
v_val_2200_ = lean_ctor_get(v_a_2196_, 0);
v___x_2201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2171_, v_numParams_2170_, v___x_2190_, v_declName_2162_, v_induct_2169_, v___x_2191_, v_a_2196_, v_val_2200_, v___x_2188_, v___x_2201_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
lean_dec(v_induct_2169_);
lean_dec(v_declName_2162_);
lean_dec_ref(v___x_2190_);
lean_dec(v_numParams_2170_);
lean_dec(v_numFields_2171_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2215_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_fst_2207_; 
v_fst_2207_ = lean_ctor_get(v_a_2203_, 0);
lean_inc(v_fst_2207_);
lean_dec(v_a_2203_);
if (lean_obj_tag(v_fst_2207_) == 0)
{
lean_object* v___x_2209_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_a_2196_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2196_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
else
{
lean_object* v_val_2211_; lean_object* v___x_2213_; 
lean_dec_ref_known(v_a_2196_, 1);
v_val_2211_ = lean_ctor_get(v_fst_2207_, 0);
lean_inc(v_val_2211_);
lean_dec_ref_known(v_fst_2207_, 1);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_val_2211_);
v___x_2213_ = v___x_2205_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_val_2211_);
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
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref_known(v_a_2196_, 1);
v_a_2216_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2202_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2202_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2225_; 
lean_dec(v_a_2196_);
lean_dec_ref(v___x_2191_);
lean_dec_ref(v___x_2190_);
lean_dec(v_numFields_2171_);
lean_dec(v_numParams_2170_);
lean_dec(v_induct_2169_);
lean_dec(v_declName_2162_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2194_);
v___x_2225_ = v___x_2198_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2194_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_dec_ref(v___x_2191_);
lean_dec_ref(v___x_2190_);
lean_dec(v_numFields_2171_);
lean_dec(v_numParams_2170_);
lean_dec(v_induct_2169_);
lean_dec(v_declName_2162_);
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec(v_a_2164_);
lean_dec(v_declName_2162_);
lean_dec_ref(v_p_2155_);
lean_dec_ref(v_e_2154_);
v___x_2232_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2232_);
v___x_2234_ = v___x_2166_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_declName_2162_);
lean_dec_ref(v_p_2155_);
lean_dec_ref(v_e_2154_);
v_a_2237_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2163_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2163_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v___x_2161_);
lean_dec_ref(v_p_2155_);
lean_dec_ref(v_e_2154_);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2247_, lean_object* v_p_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_etaStruct_x3f(v_e_2247_, v_p_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_declName_2258_, lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v_a_2261_, lean_object* v_val_2262_, lean_object* v_inst_2263_, lean_object* v_R_2264_, lean_object* v_a_2265_, lean_object* v_b_2266_, lean_object* v_c_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2255_, v___x_2256_, v___x_2257_, v_declName_2258_, v___x_2259_, v___x_2260_, v_a_2261_, v_val_2262_, v_a_2265_, v_b_2266_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2274_ = _args[0];
lean_object* v___x_2275_ = _args[1];
lean_object* v___x_2276_ = _args[2];
lean_object* v_declName_2277_ = _args[3];
lean_object* v___x_2278_ = _args[4];
lean_object* v___x_2279_ = _args[5];
lean_object* v_a_2280_ = _args[6];
lean_object* v_val_2281_ = _args[7];
lean_object* v_inst_2282_ = _args[8];
lean_object* v_R_2283_ = _args[9];
lean_object* v_a_2284_ = _args[10];
lean_object* v_b_2285_ = _args[11];
lean_object* v_c_2286_ = _args[12];
lean_object* v___y_2287_ = _args[13];
lean_object* v___y_2288_ = _args[14];
lean_object* v___y_2289_ = _args[15];
lean_object* v___y_2290_ = _args[16];
lean_object* v___y_2291_ = _args[17];
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2274_, v___x_2275_, v___x_2276_, v_declName_2277_, v___x_2278_, v___x_2279_, v_a_2280_, v_val_2281_, v_inst_2282_, v_R_2283_, v_a_2284_, v_b_2285_, v_c_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_val_2281_);
lean_dec(v_a_2280_);
lean_dec(v___x_2278_);
lean_dec(v_declName_2277_);
lean_dec_ref(v___x_2276_);
lean_dec(v___x_2275_);
lean_dec(v_upperBound_2274_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v___x_2296_; 
v___x_2296_ = l_Lean_Expr_hasMVar(v_e_2293_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v_e_2293_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; lean_object* v_mctx_2299_; lean_object* v___x_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; lean_object* v_cache_2304_; lean_object* v_zetaDeltaFVarIds_2305_; lean_object* v_postponed_2306_; lean_object* v_diag_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
v___x_2298_ = lean_st_ref_get(v___y_2294_);
v_mctx_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc_ref(v_mctx_2299_);
lean_dec(v___x_2298_);
v___x_2300_ = l_Lean_instantiateMVarsCore(v_mctx_2299_, v_e_2293_);
v_fst_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v___x_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v___x_2300_);
v___x_2303_ = lean_st_ref_take(v___y_2294_);
v_cache_2304_ = lean_ctor_get(v___x_2303_, 1);
v_zetaDeltaFVarIds_2305_ = lean_ctor_get(v___x_2303_, 2);
v_postponed_2306_ = lean_ctor_get(v___x_2303_, 3);
v_diag_2307_ = lean_ctor_get(v___x_2303_, 4);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2303_, 0);
lean_dec(v_unused_2317_);
v___x_2309_ = v___x_2303_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_diag_2307_);
lean_inc(v_postponed_2306_);
lean_inc(v_zetaDeltaFVarIds_2305_);
lean_inc(v_cache_2304_);
lean_dec(v___x_2303_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v_snd_2302_);
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_snd_2302_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_cache_2304_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_zetaDeltaFVarIds_2305_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_postponed_2306_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_diag_2307_);
v___x_2312_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_st_ref_put(v___y_2294_, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_fst_2301_);
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2318_, v___y_2319_);
lean_dec(v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2322_, v___y_2324_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_x_2346_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2353_, lean_object* v_e_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Meta_etaStruct_x3f(v_e_2354_, v_p_2353_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2380_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2380_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2380_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
if (lean_obj_tag(v_a_2361_) == 1)
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2375_; 
v_val_2365_ = lean_ctor_get(v_a_2361_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_a_2361_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2367_ = v_a_2361_;
v_isShared_2368_ = v_isSharedCheck_2375_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v_a_2361_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2375_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 0);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_val_2365_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2370_);
v___x_2372_ = v___x_2363_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_dec(v_a_2361_);
v___x_2376_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2376_);
v___x_2378_ = v___x_2363_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
v_a_2381_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2360_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2360_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2389_, lean_object* v_e_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2389_, v_e_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_apply_1(v_x_2398_, lean_box(0));
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2406_, v_x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2414_, lean_object* v_x_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_apply_1(v_x_2415_, lean_box(0));
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_m_2431_, lean_object* v_query_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
lean_object* v_zero_2436_; uint8_t v_isZero_2437_; 
v_zero_2436_ = lean_unsigned_to_nat(0u);
v_isZero_2437_ = lean_nat_dec_eq(v_x_2434_, v_zero_2436_);
if (v_isZero_2437_ == 1)
{
lean_dec(v_x_2435_);
lean_dec(v_x_2434_);
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_box(2);
return v___x_2438_;
}
else
{
lean_object* v_val_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_val_2439_ = lean_ctor_get(v_x_2433_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v_x_2433_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_val_2439_);
lean_dec(v_x_2433_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_val_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v_keyArray_2447_; lean_object* v_valueArray_2448_; lean_object* v___x_2449_; uint8_t v_isSome_2450_; 
v_keyArray_2447_ = lean_ctor_get(v_m_2431_, 1);
v_valueArray_2448_ = lean_ctor_get(v_m_2431_, 2);
v___x_2449_ = lean_array_fget_borrowed(v_keyArray_2447_, v_x_2435_);
v_isSome_2450_ = lean_noption_is_some(v___x_2449_);
if (v_isSome_2450_ == 0)
{
lean_dec(v_x_2434_);
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_x_2435_);
return v___x_2451_;
}
else
{
lean_object* v_val_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_x_2435_);
v_val_2452_ = lean_ctor_get(v_x_2433_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v_x_2433_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_val_2452_);
lean_dec(v_x_2433_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_val_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_one_2460_; lean_object* v_n_2461_; lean_object* v___y_2463_; 
v_one_2460_ = lean_unsigned_to_nat(1u);
v_n_2461_ = lean_nat_sub(v_x_2434_, v_one_2460_);
lean_dec(v_x_2434_);
if (v_isSome_2450_ == 0)
{
goto v___jp_2469_;
}
else
{
lean_object* v___x_2471_; uint8_t v_isSome_2472_; 
v___x_2471_ = lean_array_fget_borrowed(v_valueArray_2448_, v_x_2435_);
v_isSome_2472_ = lean_noption_is_some(v___x_2471_);
if (v_isSome_2472_ == 0)
{
goto v___jp_2469_;
}
else
{
lean_object* v_val_2473_; uint8_t v___x_2474_; 
lean_inc(v___x_2449_);
v_val_2473_ = lean_noption_get(v___x_2449_);
v___x_2474_ = l_Lean_ExprStructEq_beq(v_val_2473_, v_query_2432_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
lean_dec(v_val_2473_);
v___x_2475_ = lean_array_get_size(v_keyArray_2447_);
v___x_2476_ = lean_nat_add(v_x_2435_, v_one_2460_);
lean_dec(v_x_2435_);
v___x_2477_ = lean_nat_dec_lt(v___x_2476_, v___x_2475_);
if (v___x_2477_ == 0)
{
lean_dec(v___x_2476_);
v_x_2434_ = v_n_2461_;
v_x_2435_ = v_zero_2436_;
goto _start;
}
else
{
v_x_2434_ = v_n_2461_;
v_x_2435_ = v___x_2476_;
goto _start;
}
}
else
{
lean_object* v_val_2480_; lean_object* v___x_2481_; 
lean_dec(v_n_2461_);
lean_dec(v_x_2433_);
lean_inc(v___x_2471_);
v_val_2480_ = lean_noption_get(v___x_2471_);
v___x_2481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2481_, 0, v_x_2435_);
lean_ctor_set(v___x_2481_, 1, v_val_2473_);
lean_ctor_set(v___x_2481_, 2, v_val_2480_);
return v___x_2481_;
}
}
}
v___jp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2464_ = lean_array_get_size(v_keyArray_2447_);
v___x_2465_ = lean_nat_add(v_x_2435_, v_one_2460_);
lean_dec(v_x_2435_);
v___x_2466_ = lean_nat_dec_lt(v___x_2465_, v___x_2464_);
if (v___x_2466_ == 0)
{
lean_dec(v___x_2465_);
v_x_2433_ = v___y_2463_;
v_x_2434_ = v_n_2461_;
v_x_2435_ = v_zero_2436_;
goto _start;
}
else
{
v_x_2433_ = v___y_2463_;
v_x_2434_ = v_n_2461_;
v_x_2435_ = v___x_2465_;
goto _start;
}
}
v___jp_2469_:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
lean_object* v___x_2470_; 
lean_inc(v_x_2435_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_x_2435_);
v___y_2463_ = v___x_2470_;
goto v___jp_2462_;
}
else
{
v___y_2463_ = v_x_2433_;
goto v___jp_2462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_m_2482_, lean_object* v_query_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_m_2482_, v_query_2483_, v_x_2484_, v_x_2485_, v_x_2486_);
lean_dec_ref(v_query_2483_);
lean_dec_ref(v_m_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2488_, lean_object* v_query_2489_){
_start:
{
lean_object* v_keyArray_2490_; lean_object* v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v_fold_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_keyArray_2490_ = lean_ctor_get(v_m_2488_, 1);
v___x_2491_ = lean_array_get_size(v_keyArray_2490_);
v___x_2492_ = l_Lean_ExprStructEq_hash(v_query_2489_);
v___x_2493_ = 32ULL;
v___x_2494_ = lean_uint64_shift_right(v___x_2492_, v___x_2493_);
v_fold_2495_ = lean_uint64_xor(v___x_2492_, v___x_2494_);
v___x_2496_ = 16ULL;
v___x_2497_ = lean_uint64_shift_right(v_fold_2495_, v___x_2496_);
v___x_2498_ = lean_uint64_xor(v_fold_2495_, v___x_2497_);
v___x_2499_ = lean_uint64_to_usize(v___x_2498_);
v___x_2500_ = lean_usize_of_nat(v___x_2491_);
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_sub(v___x_2500_, v___x_2501_);
v___x_2503_ = lean_usize_land(v___x_2499_, v___x_2502_);
v___x_2504_ = lean_usize_to_nat(v___x_2503_);
v___x_2505_ = lean_box(0);
v___x_2506_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_m_2488_, v_query_2489_, v___x_2505_, v___x_2491_, v___x_2504_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg___boxed(lean_object* v_m_2507_, lean_object* v_query_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_2507_, v_query_2508_);
lean_dec_ref(v_query_2508_);
lean_dec_ref(v_m_2507_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg(lean_object* v_b_2510_, lean_object* v_acc_2511_, lean_object* v_i_2512_){
_start:
{
lean_object* v___y_2514_; lean_object* v_keyArray_2522_; lean_object* v_valueArray_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_keyArray_2522_ = lean_ctor_get(v_b_2510_, 1);
v_valueArray_2523_ = lean_ctor_get(v_b_2510_, 2);
v___x_2524_ = lean_array_get_size(v_keyArray_2522_);
v___x_2525_ = lean_nat_dec_lt(v_i_2512_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_dec(v_i_2512_);
return v_acc_2511_;
}
else
{
lean_object* v___x_2526_; uint8_t v_isSome_2527_; 
v___x_2526_ = lean_array_fget_borrowed(v_keyArray_2522_, v_i_2512_);
v_isSome_2527_ = lean_noption_is_some(v___x_2526_);
if (v_isSome_2527_ == 0)
{
goto v___jp_2518_;
}
else
{
lean_object* v___x_2528_; uint8_t v_isSome_2529_; 
v___x_2528_ = lean_array_fget_borrowed(v_valueArray_2523_, v_i_2512_);
v_isSome_2529_ = lean_noption_is_some(v___x_2528_);
if (v_isSome_2529_ == 0)
{
goto v___jp_2518_;
}
else
{
lean_object* v_val_2530_; lean_object* v_val_2531_; lean_object* v_i_2533_; lean_object* v___x_2538_; 
lean_inc(v___x_2526_);
v_val_2530_ = lean_noption_get(v___x_2526_);
lean_inc(v___x_2528_);
v_val_2531_ = lean_noption_get(v___x_2528_);
v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_acc_2511_, v_val_2530_);
switch(lean_obj_tag(v___x_2538_))
{
case 0:
{
lean_object* v_index_2539_; lean_object* v_size_2540_; lean_object* v___x_2541_; 
v_index_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_index_2539_);
lean_dec_ref_known(v___x_2538_, 3);
v_size_2540_ = lean_ctor_get(v_acc_2511_, 0);
lean_inc(v_size_2540_);
v___x_2541_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2511_, v_size_2540_, v_index_2539_, v_val_2530_, v_val_2531_);
lean_dec(v_index_2539_);
v___y_2514_ = v___x_2541_;
goto v___jp_2513_;
}
case 1:
{
lean_object* v_index_2542_; 
v_index_2542_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_index_2542_);
lean_dec_ref_known(v___x_2538_, 1);
v_i_2533_ = v_index_2542_;
goto v___jp_2532_;
}
default: 
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2511_, v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_index_2545_; 
v_index_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_index_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v_i_2533_ = v_index_2545_;
goto v___jp_2532_;
}
else
{
lean_dec(v_val_2531_);
lean_dec(v_val_2530_);
v___y_2514_ = v_acc_2511_;
goto v___jp_2513_;
}
}
}
v___jp_2532_:
{
lean_object* v_size_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_size_2534_ = lean_ctor_get(v_acc_2511_, 0);
v___x_2535_ = lean_unsigned_to_nat(1u);
v___x_2536_ = lean_nat_add(v_size_2534_, v___x_2535_);
v___x_2537_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2511_, v___x_2536_, v_i_2533_, v_val_2530_, v_val_2531_);
lean_dec(v_i_2533_);
v___y_2514_ = v___x_2537_;
goto v___jp_2513_;
}
}
}
}
v___jp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = lean_nat_add(v_i_2512_, v___x_2515_);
lean_dec(v_i_2512_);
v_acc_2511_ = v___y_2514_;
v_i_2512_ = v___x_2516_;
goto _start;
}
v___jp_2518_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_nat_add(v_i_2512_, v___x_2519_);
lean_dec(v_i_2512_);
v_i_2512_ = v___x_2520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg___boxed(lean_object* v_b_2546_, lean_object* v_acc_2547_, lean_object* v_i_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg(v_b_2546_, v_acc_2547_, v_i_2548_);
lean_dec_ref(v_b_2546_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg(lean_object* v_init_2550_, lean_object* v_b_2551_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg(v_b_2551_, v_init_2550_, v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg___boxed(lean_object* v_init_2554_, lean_object* v_b_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg(v_init_2554_, v_b_2555_);
lean_dec_ref(v_b_2555_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(lean_object* v_m_2557_){
_start:
{
lean_object* v_keyArray_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_cellCount_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_target_2565_; lean_object* v___x_2566_; 
v_keyArray_2558_ = lean_ctor_get(v_m_2557_, 1);
v___x_2559_ = lean_array_get_size(v_keyArray_2558_);
v___x_2560_ = lean_unsigned_to_nat(2u);
v_cellCount_2561_ = lean_nat_mul(v___x_2559_, v___x_2560_);
v___x_2562_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2561_);
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2561_);
v___x_2564_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2561_);
v_target_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2565_, 0, v___x_2562_);
lean_ctor_set(v_target_2565_, 1, v___x_2563_);
lean_ctor_set(v_target_2565_, 2, v___x_2564_);
v___x_2566_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg(v_target_2565_, v_m_2557_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg___boxed(lean_object* v_m_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(v_m_2567_);
lean_dec_ref(v_m_2567_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2569_, lean_object* v_e_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___y_2576_; lean_object* v___y_2579_; lean_object* v_i_2580_; lean_object* v___y_2596_; lean_object* v_i_2597_; lean_object* v___y_2603_; lean_object* v___x_2612_; 
v___x_2573_ = lean_st_ref_take(v_a_2569_);
v___x_2574_ = lean_box(0);
v___x_2612_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2573_, v_e_2570_);
switch(lean_obj_tag(v___x_2612_))
{
case 0:
{
lean_object* v_index_2613_; lean_object* v_size_2614_; lean_object* v___x_2615_; 
v_index_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_index_2613_);
lean_dec_ref_known(v___x_2612_, 3);
v_size_2614_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_size_2614_);
v___x_2615_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2573_, v_size_2614_, v_index_2613_, v_e_2570_, v_a_2571_);
lean_dec(v_index_2613_);
v___y_2576_ = v___x_2615_;
goto v___jp_2575_;
}
case 1:
{
lean_object* v_index_2616_; lean_object* v_size_2617_; lean_object* v_keyArray_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v_index_2616_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_index_2616_);
lean_dec_ref_known(v___x_2612_, 1);
v_size_2617_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_size_2617_);
v_keyArray_2618_ = lean_ctor_get(v___x_2573_, 1);
lean_inc_ref(v_keyArray_2618_);
v___x_2619_ = lean_unsigned_to_nat(1u);
v___x_2620_ = lean_nat_add(v_size_2617_, v___x_2619_);
lean_dec(v_size_2617_);
v___x_2621_ = lean_array_get_size(v_keyArray_2618_);
lean_dec_ref(v_keyArray_2618_);
v___x_2622_ = lean_nat_dec_lt(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec(v___x_2620_);
lean_dec(v_index_2616_);
goto v___jp_2585_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2623_ = lean_unsigned_to_nat(4u);
v___x_2624_ = lean_nat_mul(v___x_2620_, v___x_2623_);
v___x_2625_ = lean_unsigned_to_nat(3u);
v___x_2626_ = lean_nat_mul(v___x_2621_, v___x_2625_);
v___x_2627_ = lean_nat_dec_le(v___x_2624_, v___x_2626_);
lean_dec(v___x_2626_);
lean_dec(v___x_2624_);
if (v___x_2627_ == 0)
{
lean_dec(v___x_2620_);
lean_dec(v_index_2616_);
goto v___jp_2585_;
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2573_, v___x_2620_, v_index_2616_, v_e_2570_, v_a_2571_);
lean_dec(v_index_2616_);
v___y_2576_ = v___x_2628_;
goto v___jp_2575_;
}
}
}
default: 
{
lean_object* v_size_2629_; lean_object* v_keyArray_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v_size_2629_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_size_2629_);
v_keyArray_2630_ = lean_ctor_get(v___x_2573_, 1);
lean_inc_ref(v_keyArray_2630_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_add(v_size_2629_, v___x_2631_);
lean_dec(v_size_2629_);
v___x_2633_ = lean_array_get_size(v_keyArray_2630_);
lean_dec_ref(v_keyArray_2630_);
v___x_2634_ = lean_nat_dec_lt(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
lean_dec(v___x_2632_);
v___x_2635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(v___x_2573_);
lean_dec(v___x_2573_);
v___y_2603_ = v___x_2635_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2636_ = lean_unsigned_to_nat(4u);
v___x_2637_ = lean_nat_mul(v___x_2632_, v___x_2636_);
lean_dec(v___x_2632_);
v___x_2638_ = lean_unsigned_to_nat(3u);
v___x_2639_ = lean_nat_mul(v___x_2633_, v___x_2638_);
v___x_2640_ = lean_nat_dec_le(v___x_2637_, v___x_2639_);
lean_dec(v___x_2639_);
lean_dec(v___x_2637_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(v___x_2573_);
lean_dec(v___x_2573_);
v___y_2603_ = v___x_2641_;
goto v___jp_2602_;
}
else
{
v___y_2603_ = v___x_2573_;
goto v___jp_2602_;
}
}
}
}
v___jp_2575_:
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_st_ref_put(v_a_2569_, v___y_2576_);
return v___x_2574_;
}
v___jp_2578_:
{
lean_object* v_size_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_size_2581_ = lean_ctor_get(v___y_2579_, 0);
v___x_2582_ = lean_unsigned_to_nat(1u);
v___x_2583_ = lean_nat_add(v_size_2581_, v___x_2582_);
v___x_2584_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2579_, v___x_2583_, v_i_2580_, v_e_2570_, v_a_2571_);
lean_dec(v_i_2580_);
v___y_2576_ = v___x_2584_;
goto v___jp_2575_;
}
v___jp_2585_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(v___x_2573_);
lean_dec(v___x_2573_);
v___x_2587_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2586_, v_e_2570_);
switch(lean_obj_tag(v___x_2587_))
{
case 0:
{
lean_object* v_index_2588_; lean_object* v_size_2589_; lean_object* v___x_2590_; 
v_index_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_index_2588_);
lean_dec_ref_known(v___x_2587_, 3);
v_size_2589_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_size_2589_);
v___x_2590_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2586_, v_size_2589_, v_index_2588_, v_e_2570_, v_a_2571_);
lean_dec(v_index_2588_);
v___y_2576_ = v___x_2590_;
goto v___jp_2575_;
}
case 1:
{
lean_object* v_index_2591_; 
v_index_2591_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_index_2591_);
lean_dec_ref_known(v___x_2587_, 1);
v___y_2579_ = v___x_2586_;
v_i_2580_ = v_index_2591_;
goto v___jp_2578_;
}
default: 
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2586_, v___x_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_index_2594_; 
v_index_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_index_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___y_2579_ = v___x_2586_;
v_i_2580_ = v_index_2594_;
goto v___jp_2578_;
}
else
{
lean_dec_ref(v_a_2571_);
lean_dec_ref(v_e_2570_);
v___y_2576_ = v___x_2586_;
goto v___jp_2575_;
}
}
}
}
v___jp_2595_:
{
lean_object* v_size_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_size_2598_ = lean_ctor_get(v___y_2596_, 0);
v___x_2599_ = lean_unsigned_to_nat(1u);
v___x_2600_ = lean_nat_add(v_size_2598_, v___x_2599_);
v___x_2601_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2596_, v___x_2600_, v_i_2597_, v_e_2570_, v_a_2571_);
lean_dec(v_i_2597_);
v___y_2576_ = v___x_2601_;
goto v___jp_2575_;
}
v___jp_2602_:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___y_2603_, v_e_2570_);
switch(lean_obj_tag(v___x_2604_))
{
case 0:
{
lean_object* v_index_2605_; lean_object* v_size_2606_; lean_object* v___x_2607_; 
v_index_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_index_2605_);
lean_dec_ref_known(v___x_2604_, 3);
v_size_2606_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_size_2606_);
v___x_2607_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2603_, v_size_2606_, v_index_2605_, v_e_2570_, v_a_2571_);
lean_dec(v_index_2605_);
v___y_2576_ = v___x_2607_;
goto v___jp_2575_;
}
case 1:
{
lean_object* v_index_2608_; 
v_index_2608_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_index_2608_);
lean_dec_ref_known(v___x_2604_, 1);
v___y_2596_ = v___y_2603_;
v_i_2597_ = v_index_2608_;
goto v___jp_2595_;
}
default: 
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2603_, v___x_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_index_2611_; 
v_index_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_index_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___y_2596_ = v___y_2603_;
v_i_2597_ = v_index_2611_;
goto v___jp_2595_;
}
else
{
lean_dec_ref(v_a_2571_);
lean_dec_ref(v_e_2570_);
v___y_2576_ = v___y_2603_;
goto v___jp_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2642_, lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2642_, v_e_2643_, v_a_2644_);
lean_dec(v_a_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_m_2647_, lean_object* v_query_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_2647_, v_query_2648_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_index_2650_; lean_object* v_key_2651_; lean_object* v_value_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_index_2650_ = lean_ctor_get(v___x_2649_, 0);
v_key_2651_ = lean_ctor_get(v___x_2649_, 1);
v_value_2652_ = lean_ctor_get(v___x_2649_, 2);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2649_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_value_2652_);
lean_inc(v_key_2651_);
lean_inc(v_index_2650_);
lean_dec(v___x_2649_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_index_2650_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_key_2651_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_value_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
else
{
lean_object* v___x_2660_; 
lean_dec(v___x_2649_);
v___x_2660_ = lean_box(1);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_m_2661_, lean_object* v_query_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_m_2661_, v_query_2662_);
lean_dec_ref(v_query_2662_);
lean_dec_ref(v_m_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_m_2664_, v_a_2665_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_value_2667_; lean_object* v___x_2668_; 
v_value_2667_ = lean_ctor_get(v___x_2666_, 2);
lean_inc(v_value_2667_);
lean_dec_ref_known(v___x_2666_, 3);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_value_2667_);
return v___x_2668_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_box(0);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2670_, v_a_2671_);
lean_dec_ref(v_a_2671_);
lean_dec_ref(v_m_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2673_, lean_object* v___y_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
lean_inc(v___y_2679_);
lean_inc_ref(v___y_2678_);
lean_inc(v___y_2677_);
lean_inc_ref(v___y_2676_);
lean_inc(v___y_2674_);
v___x_2681_ = lean_apply_7(v_k_2673_, v_b_2675_, v___y_2674_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, lean_box(0));
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2682_, lean_object* v___y_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2682_, v___y_2683_, v_b_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2683_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2691_, uint8_t v_bi_2692_, lean_object* v_type_2693_, lean_object* v_k_2694_, uint8_t v_kind_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___f_2702_; lean_object* v___x_2703_; 
lean_inc(v___y_2696_);
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2702_, 0, v_k_2694_);
lean_closure_set(v___f_2702_, 1, v___y_2696_);
v___x_2703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2691_, v_bi_2692_, v_type_2693_, v___f_2702_, v_kind_2695_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2703_) == 0)
{
return v___x_2703_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2712_, lean_object* v_bi_2713_, lean_object* v_type_2714_, lean_object* v_k_2715_, lean_object* v_kind_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v_bi_boxed_2723_; uint8_t v_kind_boxed_2724_; lean_object* v_res_2725_; 
v_bi_boxed_2723_ = lean_unbox(v_bi_2713_);
v_kind_boxed_2724_ = lean_unbox(v_kind_2716_);
v_res_2725_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2712_, v_bi_boxed_2723_, v_type_2714_, v_k_2715_, v_kind_boxed_2724_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2726_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2740_, lean_object* v_type_2741_, lean_object* v_val_2742_, lean_object* v_k_2743_, uint8_t v_nondep_2744_, uint8_t v_kind_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___f_2752_; lean_object* v___x_2753_; 
lean_inc(v___y_2746_);
v___f_2752_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2752_, 0, v_k_2743_);
lean_closure_set(v___f_2752_, 1, v___y_2746_);
v___x_2753_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2740_, v_type_2741_, v_val_2742_, v___f_2752_, v_nondep_2744_, v_kind_2745_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2753_) == 0)
{
return v___x_2753_;
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2762_, lean_object* v_type_2763_, lean_object* v_val_2764_, lean_object* v_k_2765_, lean_object* v_nondep_2766_, lean_object* v_kind_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v_nondep_boxed_2774_; uint8_t v_kind_boxed_2775_; lean_object* v_res_2776_; 
v_nondep_boxed_2774_ = lean_unbox(v_nondep_2766_);
v_kind_boxed_2775_ = lean_unbox(v_kind_2767_);
v_res_2776_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2762_, v_type_2763_, v_val_2764_, v_k_2765_, v_nondep_boxed_2774_, v_kind_boxed_2775_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
return v_res_2776_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = l_Lean_maxRecDepthErrorMessage;
v___x_2783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2785_ = l_Lean_MessageData_ofFormat(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2786_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2787_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2788_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v___x_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2789_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_ref_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___y_2805_; lean_object* v_fileName_2814_; lean_object* v_fileMap_2815_; lean_object* v_options_2816_; lean_object* v_currRecDepth_2817_; lean_object* v_maxRecDepth_2818_; lean_object* v_ref_2819_; lean_object* v_currNamespace_2820_; lean_object* v_openDecls_2821_; lean_object* v_initHeartbeats_2822_; lean_object* v_maxHeartbeats_2823_; lean_object* v_quotContext_2824_; lean_object* v_currMacroScope_2825_; uint8_t v_diag_2826_; lean_object* v_cancelTk_x3f_2827_; uint8_t v_suppressElabErrors_2828_; lean_object* v_inheritedTraceOptions_2829_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v_fileName_2814_ = lean_ctor_get(v___y_2801_, 0);
v_fileMap_2815_ = lean_ctor_get(v___y_2801_, 1);
v_options_2816_ = lean_ctor_get(v___y_2801_, 2);
v_currRecDepth_2817_ = lean_ctor_get(v___y_2801_, 3);
v_maxRecDepth_2818_ = lean_ctor_get(v___y_2801_, 4);
v_ref_2819_ = lean_ctor_get(v___y_2801_, 5);
v_currNamespace_2820_ = lean_ctor_get(v___y_2801_, 6);
v_openDecls_2821_ = lean_ctor_get(v___y_2801_, 7);
v_initHeartbeats_2822_ = lean_ctor_get(v___y_2801_, 8);
v_maxHeartbeats_2823_ = lean_ctor_get(v___y_2801_, 9);
v_quotContext_2824_ = lean_ctor_get(v___y_2801_, 10);
v_currMacroScope_2825_ = lean_ctor_get(v___y_2801_, 11);
v_diag_2826_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14);
v_cancelTk_x3f_2827_ = lean_ctor_get(v___y_2801_, 12);
v_suppressElabErrors_2828_ = lean_ctor_get_uint8(v___y_2801_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2829_ = lean_ctor_get(v___y_2801_, 13);
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_nat_dec_eq(v_maxRecDepth_2818_, v___x_2835_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_eq(v_currRecDepth_2817_, v_maxRecDepth_2818_);
if (v___x_2837_ == 0)
{
goto v___jp_2830_;
}
else
{
lean_object* v___x_2838_; 
lean_dec_ref(v_x_2797_);
lean_inc(v_ref_2819_);
v___x_2838_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2819_);
v___y_2805_ = v___x_2838_;
goto v___jp_2804_;
}
}
else
{
goto v___jp_2830_;
}
v___jp_2804_:
{
if (lean_obj_tag(v___y_2805_) == 0)
{
return v___y_2805_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___y_2805_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___y_2805_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___y_2805_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___y_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
v___jp_2830_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_add(v_currRecDepth_2817_, v___x_2831_);
lean_inc_ref(v_inheritedTraceOptions_2829_);
lean_inc(v_cancelTk_x3f_2827_);
lean_inc(v_currMacroScope_2825_);
lean_inc(v_quotContext_2824_);
lean_inc(v_maxHeartbeats_2823_);
lean_inc(v_initHeartbeats_2822_);
lean_inc(v_openDecls_2821_);
lean_inc(v_currNamespace_2820_);
lean_inc(v_ref_2819_);
lean_inc(v_maxRecDepth_2818_);
lean_inc_ref(v_options_2816_);
lean_inc_ref(v_fileMap_2815_);
lean_inc_ref(v_fileName_2814_);
v___x_2833_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2833_, 0, v_fileName_2814_);
lean_ctor_set(v___x_2833_, 1, v_fileMap_2815_);
lean_ctor_set(v___x_2833_, 2, v_options_2816_);
lean_ctor_set(v___x_2833_, 3, v___x_2832_);
lean_ctor_set(v___x_2833_, 4, v_maxRecDepth_2818_);
lean_ctor_set(v___x_2833_, 5, v_ref_2819_);
lean_ctor_set(v___x_2833_, 6, v_currNamespace_2820_);
lean_ctor_set(v___x_2833_, 7, v_openDecls_2821_);
lean_ctor_set(v___x_2833_, 8, v_initHeartbeats_2822_);
lean_ctor_set(v___x_2833_, 9, v_maxHeartbeats_2823_);
lean_ctor_set(v___x_2833_, 10, v_quotContext_2824_);
lean_ctor_set(v___x_2833_, 11, v_currMacroScope_2825_);
lean_ctor_set(v___x_2833_, 12, v_cancelTk_x3f_2827_);
lean_ctor_set(v___x_2833_, 13, v_inheritedTraceOptions_2829_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*14, v_diag_2826_);
lean_ctor_set_uint8(v___x_2833_, sizeof(void*)*14 + 1, v_suppressElabErrors_2828_);
lean_inc(v___y_2802_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc(v___y_2798_);
v___x_2834_ = lean_apply_6(v_x_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___x_2833_, v___y_2802_, lean_box(0));
v___y_2805_ = v___x_2834_;
goto v___jp_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2850_, lean_object* v_pre_2851_, lean_object* v_post_2852_, uint8_t v_usedLetOnly_2853_, uint8_t v_skipConstInApp_2854_, uint8_t v_skipInstances_2855_, lean_object* v_body_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_array_push(v_fvars_2850_, v_x_2857_);
v___x_2865_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v___x_2864_, v_body_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2866_, lean_object* v_pre_2867_, lean_object* v_post_2868_, lean_object* v_usedLetOnly_2869_, lean_object* v_skipConstInApp_2870_, lean_object* v_skipInstances_2871_, lean_object* v_body_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
uint8_t v_usedLetOnly_boxed_2880_; uint8_t v_skipConstInApp_boxed_2881_; uint8_t v_skipInstances_boxed_2882_; lean_object* v_res_2883_; 
v_usedLetOnly_boxed_2880_ = lean_unbox(v_usedLetOnly_2869_);
v_skipConstInApp_boxed_2881_ = lean_unbox(v_skipConstInApp_2870_);
v_skipInstances_boxed_2882_ = lean_unbox(v_skipInstances_2871_);
v_res_2883_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2866_, v_pre_2867_, v_post_2868_, v_usedLetOnly_boxed_2880_, v_skipConstInApp_boxed_2881_, v_skipInstances_boxed_2882_, v_body_2872_, v_x_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2884_, lean_object* v_post_2885_, uint8_t v_usedLetOnly_2886_, uint8_t v_skipConstInApp_2887_, uint8_t v_skipInstances_2888_, lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
lean_inc_ref(v_post_2885_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
lean_inc_ref(v_e_2889_);
v___x_2896_ = lean_apply_6(v_post_2885_, v_e_2889_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, lean_box(0));
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2915_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2915_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2915_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
switch(lean_obj_tag(v_a_2897_))
{
case 0:
{
lean_object* v_e_2901_; lean_object* v___x_2903_; 
lean_dec_ref(v_e_2889_);
lean_dec_ref(v_post_2885_);
lean_dec_ref(v_pre_2884_);
v_e_2901_ = lean_ctor_get(v_a_2897_, 0);
lean_inc_ref(v_e_2901_);
lean_dec_ref_known(v_a_2897_, 1);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v_e_2901_);
v___x_2903_ = v___x_2899_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_e_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
case 1:
{
lean_object* v_e_2905_; lean_object* v___x_2906_; 
lean_del_object(v___x_2899_);
lean_dec_ref(v_e_2889_);
v_e_2905_ = lean_ctor_get(v_a_2897_, 0);
lean_inc_ref(v_e_2905_);
lean_dec_ref_known(v_a_2897_, 1);
v___x_2906_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2884_, v_post_2885_, v_usedLetOnly_2886_, v_skipConstInApp_2887_, v_skipInstances_2888_, v_e_2905_, v_a_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2906_;
}
default: 
{
lean_object* v_e_x3f_2907_; 
lean_dec_ref(v_post_2885_);
lean_dec_ref(v_pre_2884_);
v_e_x3f_2907_ = lean_ctor_get(v_a_2897_, 0);
lean_inc(v_e_x3f_2907_);
lean_dec_ref_known(v_a_2897_, 1);
if (lean_obj_tag(v_e_x3f_2907_) == 0)
{
lean_object* v___x_2909_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v_e_2889_);
v___x_2909_ = v___x_2899_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_e_2889_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
else
{
lean_object* v_val_2911_; lean_object* v___x_2913_; 
lean_dec_ref(v_e_2889_);
v_val_2911_ = lean_ctor_get(v_e_x3f_2907_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v_e_x3f_2907_, 1);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v_val_2911_);
v___x_2913_ = v___x_2899_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_val_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_e_2889_);
lean_dec_ref(v_post_2885_);
lean_dec_ref(v_pre_2884_);
v_a_2916_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2896_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2896_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2924_, lean_object* v_post_2925_, uint8_t v_usedLetOnly_2926_, uint8_t v_skipConstInApp_2927_, uint8_t v_skipInstances_2928_, lean_object* v_fvars_2929_, lean_object* v_e_2930_, lean_object* v_a_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
if (lean_obj_tag(v_e_2930_) == 6)
{
lean_object* v_binderName_2937_; lean_object* v_binderType_2938_; lean_object* v_body_2939_; uint8_t v_binderInfo_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_binderName_2937_ = lean_ctor_get(v_e_2930_, 0);
lean_inc(v_binderName_2937_);
v_binderType_2938_ = lean_ctor_get(v_e_2930_, 1);
lean_inc_ref(v_binderType_2938_);
v_body_2939_ = lean_ctor_get(v_e_2930_, 2);
lean_inc_ref(v_body_2939_);
v_binderInfo_2940_ = lean_ctor_get_uint8(v_e_2930_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2930_, 3);
v___x_2941_ = lean_expr_instantiate_rev(v_binderType_2938_, v_fvars_2929_);
lean_dec_ref(v_binderType_2938_);
lean_inc_ref(v_post_2925_);
lean_inc_ref(v_pre_2924_);
v___x_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2924_, v_post_2925_, v_usedLetOnly_2926_, v_skipConstInApp_2927_, v_skipInstances_2928_, v___x_2941_, v_a_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = lean_box(v_usedLetOnly_2926_);
v___x_2945_ = lean_box(v_skipConstInApp_2927_);
v___x_2946_ = lean_box(v_skipInstances_2928_);
v___f_2947_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2947_, 0, v_fvars_2929_);
lean_closure_set(v___f_2947_, 1, v_pre_2924_);
lean_closure_set(v___f_2947_, 2, v_post_2925_);
lean_closure_set(v___f_2947_, 3, v___x_2944_);
lean_closure_set(v___f_2947_, 4, v___x_2945_);
lean_closure_set(v___f_2947_, 5, v___x_2946_);
lean_closure_set(v___f_2947_, 6, v_body_2939_);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2937_, v_binderInfo_2940_, v_a_2943_, v___f_2947_, v___x_2948_, v_a_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
return v___x_2949_;
}
else
{
lean_dec_ref(v_body_2939_);
lean_dec(v_binderName_2937_);
lean_dec_ref(v_fvars_2929_);
lean_dec_ref(v_post_2925_);
lean_dec_ref(v_pre_2924_);
return v___x_2942_;
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_expr_instantiate_rev(v_e_2930_, v_fvars_2929_);
lean_dec_ref(v_e_2930_);
lean_inc_ref(v_post_2925_);
lean_inc_ref(v_pre_2924_);
v___x_2951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2924_, v_post_2925_, v_usedLetOnly_2926_, v_skipConstInApp_2927_, v_skipInstances_2928_, v___x_2950_, v_a_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; uint8_t v___x_2953_; uint8_t v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = 0;
v___x_2954_ = 1;
v___x_2955_ = 1;
v___x_2956_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2929_, v_a_2952_, v___x_2953_, v_usedLetOnly_2926_, v___x_2953_, v___x_2954_, v___x_2955_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec_ref(v_fvars_2929_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2924_, v_post_2925_, v_usedLetOnly_2926_, v_skipConstInApp_2927_, v_skipInstances_2928_, v_a_2957_, v_a_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
return v___x_2958_;
}
else
{
lean_dec_ref(v_post_2925_);
lean_dec_ref(v_pre_2924_);
return v___x_2956_;
}
}
else
{
lean_dec_ref(v_fvars_2929_);
lean_dec_ref(v_post_2925_);
lean_dec_ref(v_pre_2924_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2959_, lean_object* v_pre_2960_, lean_object* v_post_2961_, uint8_t v_usedLetOnly_2962_, uint8_t v_skipConstInApp_2963_, uint8_t v_skipInstances_2964_, lean_object* v_body_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_array_push(v_fvars_2959_, v_x_2966_);
v___x_2974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2960_, v_post_2961_, v_usedLetOnly_2962_, v_skipConstInApp_2963_, v_skipInstances_2964_, v___x_2973_, v_body_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2975_, lean_object* v_pre_2976_, lean_object* v_post_2977_, lean_object* v_usedLetOnly_2978_, lean_object* v_skipConstInApp_2979_, lean_object* v_skipInstances_2980_, lean_object* v_body_2981_, lean_object* v_x_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_usedLetOnly_boxed_2989_; uint8_t v_skipConstInApp_boxed_2990_; uint8_t v_skipInstances_boxed_2991_; lean_object* v_res_2992_; 
v_usedLetOnly_boxed_2989_ = lean_unbox(v_usedLetOnly_2978_);
v_skipConstInApp_boxed_2990_ = lean_unbox(v_skipConstInApp_2979_);
v_skipInstances_boxed_2991_ = lean_unbox(v_skipInstances_2980_);
v_res_2992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2975_, v_pre_2976_, v_post_2977_, v_usedLetOnly_boxed_2989_, v_skipConstInApp_boxed_2990_, v_skipInstances_boxed_2991_, v_body_2981_, v_x_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2993_, lean_object* v_post_2994_, uint8_t v_usedLetOnly_2995_, uint8_t v_skipConstInApp_2996_, uint8_t v_skipInstances_2997_, lean_object* v_fvars_2998_, lean_object* v_e_2999_, lean_object* v_a_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
if (lean_obj_tag(v_e_2999_) == 8)
{
lean_object* v_declName_3006_; lean_object* v_type_3007_; lean_object* v_value_3008_; lean_object* v_body_3009_; uint8_t v_nondep_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_declName_3006_ = lean_ctor_get(v_e_2999_, 0);
lean_inc(v_declName_3006_);
v_type_3007_ = lean_ctor_get(v_e_2999_, 1);
lean_inc_ref(v_type_3007_);
v_value_3008_ = lean_ctor_get(v_e_2999_, 2);
lean_inc_ref(v_value_3008_);
v_body_3009_ = lean_ctor_get(v_e_2999_, 3);
lean_inc_ref(v_body_3009_);
v_nondep_3010_ = lean_ctor_get_uint8(v_e_2999_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2999_, 4);
v___x_3011_ = lean_expr_instantiate_rev(v_type_3007_, v_fvars_2998_);
lean_dec_ref(v_type_3007_);
lean_inc_ref(v_post_2994_);
lean_inc_ref(v_pre_2993_);
v___x_3012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v___x_3011_, v_a_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_expr_instantiate_rev(v_value_3008_, v_fvars_2998_);
lean_dec_ref(v_value_3008_);
lean_inc_ref(v_post_2994_);
lean_inc_ref(v_pre_2993_);
v___x_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v___x_3014_, v_a_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___f_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_box(v_usedLetOnly_2995_);
v___x_3018_ = lean_box(v_skipConstInApp_2996_);
v___x_3019_ = lean_box(v_skipInstances_2997_);
v___f_3020_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3020_, 0, v_fvars_2998_);
lean_closure_set(v___f_3020_, 1, v_pre_2993_);
lean_closure_set(v___f_3020_, 2, v_post_2994_);
lean_closure_set(v___f_3020_, 3, v___x_3017_);
lean_closure_set(v___f_3020_, 4, v___x_3018_);
lean_closure_set(v___f_3020_, 5, v___x_3019_);
lean_closure_set(v___f_3020_, 6, v_body_3009_);
v___x_3021_ = 0;
v___x_3022_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_3006_, v_a_3013_, v_a_3016_, v___f_3020_, v_nondep_3010_, v___x_3021_, v_a_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3022_;
}
else
{
lean_dec(v_a_3013_);
lean_dec_ref(v_body_3009_);
lean_dec(v_declName_3006_);
lean_dec_ref(v_fvars_2998_);
lean_dec_ref(v_post_2994_);
lean_dec_ref(v_pre_2993_);
return v___x_3015_;
}
}
else
{
lean_dec_ref(v_body_3009_);
lean_dec_ref(v_value_3008_);
lean_dec(v_declName_3006_);
lean_dec_ref(v_fvars_2998_);
lean_dec_ref(v_post_2994_);
lean_dec_ref(v_pre_2993_);
return v___x_3012_;
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_expr_instantiate_rev(v_e_2999_, v_fvars_2998_);
lean_dec_ref(v_e_2999_);
lean_inc_ref(v_post_2994_);
lean_inc_ref(v_pre_2993_);
v___x_3024_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v___x_3023_, v_a_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; uint8_t v___x_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = 0;
v___x_3027_ = 1;
v___x_3028_ = l_Lean_Meta_mkLetFVars(v_fvars_2998_, v_a_3025_, v_usedLetOnly_2995_, v___x_3026_, v___x_3027_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec_ref(v_fvars_2998_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3030_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
v___x_3030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v_a_3029_, v_a_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3030_;
}
else
{
lean_dec_ref(v_post_2994_);
lean_dec_ref(v_pre_2993_);
return v___x_3028_;
}
}
else
{
lean_dec_ref(v_fvars_2998_);
lean_dec_ref(v_post_2994_);
lean_dec_ref(v_pre_2993_);
return v___x_3024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3031_, lean_object* v_post_3032_, uint8_t v_usedLetOnly_3033_, uint8_t v_skipConstInApp_3034_, uint8_t v_skipInstances_3035_, size_t v_sz_3036_, size_t v_i_3037_, lean_object* v_bs_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v___x_3045_; 
v___x_3045_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
lean_dec_ref(v_post_3032_);
lean_dec_ref(v_pre_3031_);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_bs_3038_);
return v___x_3046_;
}
else
{
lean_object* v_v_3047_; lean_object* v___x_3048_; 
v_v_3047_ = lean_array_uget_borrowed(v_bs_3038_, v_i_3037_);
lean_inc(v_v_3047_);
lean_inc_ref(v_post_3032_);
lean_inc_ref(v_pre_3031_);
v___x_3048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3031_, v_post_3032_, v_usedLetOnly_3033_, v_skipConstInApp_3034_, v_skipInstances_3035_, v_v_3047_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; lean_object* v_bs_x27_3051_; size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = lean_unsigned_to_nat(0u);
v_bs_x27_3051_ = lean_array_uset(v_bs_3038_, v_i_3037_, v___x_3050_);
v___x_3052_ = ((size_t)1ULL);
v___x_3053_ = lean_usize_add(v_i_3037_, v___x_3052_);
v___x_3054_ = lean_array_uset(v_bs_x27_3051_, v_i_3037_, v_a_3049_);
v_i_3037_ = v___x_3053_;
v_bs_3038_ = v___x_3054_;
goto _start;
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_bs_3038_);
lean_dec_ref(v_post_3032_);
lean_dec_ref(v_pre_3031_);
v_a_3056_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3048_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3048_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3064_, lean_object* v_post_3065_, uint8_t v_usedLetOnly_3066_, uint8_t v_skipConstInApp_3067_, uint8_t v_skipInstances_3068_, lean_object* v___x_3069_, lean_object* v___y_3070_, lean_object* v_b_3071_, lean_object* v_a_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3064_, v_post_3065_, v_usedLetOnly_3066_, v_skipConstInApp_3067_, v_skipInstances_3068_, v___x_3069_, v___y_3070_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3088_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3083_ = lean_array_fset(v_b_3071_, v_a_3072_, v_a_3079_);
v___x_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3084_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v_b_3071_);
v_a_3089_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3078_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3078_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3097_, lean_object* v_post_3098_, lean_object* v_usedLetOnly_3099_, lean_object* v_skipConstInApp_3100_, lean_object* v_skipInstances_3101_, lean_object* v___x_3102_, lean_object* v___y_3103_, lean_object* v_b_3104_, lean_object* v_a_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v_usedLetOnly_boxed_3111_; uint8_t v_skipConstInApp_boxed_3112_; uint8_t v_skipInstances_boxed_3113_; lean_object* v_res_3114_; 
v_usedLetOnly_boxed_3111_ = lean_unbox(v_usedLetOnly_3099_);
v_skipConstInApp_boxed_3112_ = lean_unbox(v_skipConstInApp_3100_);
v_skipInstances_boxed_3113_ = lean_unbox(v_skipInstances_3101_);
v_res_3114_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3097_, v_post_3098_, v_usedLetOnly_boxed_3111_, v_skipConstInApp_boxed_3112_, v_skipInstances_boxed_3113_, v___x_3102_, v___y_3103_, v_b_3104_, v_a_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v_a_3105_);
lean_dec(v___y_3103_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3115_, lean_object* v___x_3116_, lean_object* v_pre_3117_, lean_object* v_post_3118_, uint8_t v_usedLetOnly_3119_, uint8_t v_skipConstInApp_3120_, uint8_t v_skipInstances_3121_, lean_object* v_a_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___y_3131_; uint8_t v___x_3154_; 
v___x_3154_ = lean_nat_dec_lt(v_a_3122_, v_upperBound_3115_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
lean_dec(v_a_3122_);
lean_dec_ref(v_post_3118_);
lean_dec_ref(v_pre_3117_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v_b_3123_);
return v___x_3155_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3156_ = lean_array_fget_borrowed(v_b_3123_, v_a_3122_);
v___x_3157_ = lean_array_get_size(v___x_3116_);
v___x_3158_ = lean_nat_dec_lt(v_a_3122_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___f_3162_; 
lean_inc(v___x_3156_);
v___x_3159_ = lean_box(v_usedLetOnly_3119_);
v___x_3160_ = lean_box(v_skipConstInApp_3120_);
v___x_3161_ = lean_box(v_skipInstances_3121_);
lean_inc(v_a_3122_);
lean_inc(v___y_3124_);
lean_inc_ref(v_post_3118_);
lean_inc_ref(v_pre_3117_);
v___f_3162_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3162_, 0, v_pre_3117_);
lean_closure_set(v___f_3162_, 1, v_post_3118_);
lean_closure_set(v___f_3162_, 2, v___x_3159_);
lean_closure_set(v___f_3162_, 3, v___x_3160_);
lean_closure_set(v___f_3162_, 4, v___x_3161_);
lean_closure_set(v___f_3162_, 5, v___x_3156_);
lean_closure_set(v___f_3162_, 6, v___y_3124_);
lean_closure_set(v___f_3162_, 7, v_b_3123_);
lean_closure_set(v___f_3162_, 8, v_a_3122_);
v___y_3131_ = v___f_3162_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3163_; uint8_t v_isInstance_3164_; 
v___x_3163_ = lean_array_fget_borrowed(v___x_3116_, v_a_3122_);
v_isInstance_3164_ = lean_ctor_get_uint8(v___x_3163_, sizeof(void*)*1 + 4);
if (v_isInstance_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___f_3168_; 
lean_inc(v___x_3156_);
v___x_3165_ = lean_box(v_usedLetOnly_3119_);
v___x_3166_ = lean_box(v_skipConstInApp_3120_);
v___x_3167_ = lean_box(v_skipInstances_3121_);
lean_inc(v_a_3122_);
lean_inc(v___y_3124_);
lean_inc_ref(v_post_3118_);
lean_inc_ref(v_pre_3117_);
v___f_3168_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3168_, 0, v_pre_3117_);
lean_closure_set(v___f_3168_, 1, v_post_3118_);
lean_closure_set(v___f_3168_, 2, v___x_3165_);
lean_closure_set(v___f_3168_, 3, v___x_3166_);
lean_closure_set(v___f_3168_, 4, v___x_3167_);
lean_closure_set(v___f_3168_, 5, v___x_3156_);
lean_closure_set(v___f_3168_, 6, v___y_3124_);
lean_closure_set(v___f_3168_, 7, v_b_3123_);
lean_closure_set(v___f_3168_, 8, v_a_3122_);
v___y_3131_ = v___f_3168_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3169_; lean_object* v___f_3170_; 
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_b_3123_);
v___f_3170_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3170_, 0, v___x_3169_);
v___y_3131_ = v___f_3170_;
goto v___jp_3130_;
}
}
}
v___jp_3130_:
{
lean_object* v___x_3132_; 
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3132_ = lean_apply_5(v___y_3131_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3145_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3145_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3145_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
if (lean_obj_tag(v_a_3133_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; 
lean_dec(v_a_3122_);
lean_dec_ref(v_post_3118_);
lean_dec_ref(v_pre_3117_);
v_a_3137_ = lean_ctor_get(v_a_3133_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v_a_3133_, 1);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_a_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_del_object(v___x_3135_);
v_a_3141_ = lean_ctor_get(v_a_3133_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v_a_3133_, 1);
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_add(v_a_3122_, v___x_3142_);
lean_dec(v_a_3122_);
v_a_3122_ = v___x_3143_;
v_b_3123_ = v_a_3141_;
goto _start;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_3122_);
lean_dec_ref(v_post_3118_);
lean_dec_ref(v_pre_3117_);
v_a_3146_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3132_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3132_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3171_, lean_object* v_pre_3172_, lean_object* v_post_3173_, uint8_t v_usedLetOnly_3174_, uint8_t v_skipConstInApp_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_f_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; 
if (lean_obj_tag(v_x_3176_) == 5)
{
lean_object* v_fn_3234_; lean_object* v_arg_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_fn_3234_ = lean_ctor_get(v_x_3176_, 0);
lean_inc_ref(v_fn_3234_);
v_arg_3235_ = lean_ctor_get(v_x_3176_, 1);
lean_inc_ref(v_arg_3235_);
lean_dec_ref_known(v_x_3176_, 2);
v___x_3236_ = lean_array_set(v_x_3177_, v_x_3178_, v_arg_3235_);
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_sub(v_x_3178_, v___x_3237_);
lean_dec(v_x_3178_);
v_x_3176_ = v_fn_3234_;
v_x_3177_ = v___x_3236_;
v_x_3178_ = v___x_3238_;
goto _start;
}
else
{
lean_dec(v_x_3178_);
if (v_skipConstInApp_3175_ == 0)
{
goto v___jp_3231_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = l_Lean_Expr_isConst(v_x_3176_);
if (v___x_3240_ == 0)
{
goto v___jp_3231_;
}
else
{
v_f_3186_ = v_x_3176_;
v___y_3187_ = v___y_3179_;
v___y_3188_ = v___y_3180_;
v___y_3189_ = v___y_3181_;
v___y_3190_ = v___y_3182_;
v___y_3191_ = v___y_3183_;
goto v___jp_3185_;
}
}
}
v___jp_3185_:
{
if (v_skipInstances_3171_ == 0)
{
size_t v_sz_3192_; size_t v___x_3193_; lean_object* v___x_3194_; 
v_sz_3192_ = lean_array_size(v_x_3177_);
v___x_3193_ = ((size_t)0ULL);
lean_inc_ref(v_post_3173_);
lean_inc_ref(v_pre_3172_);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3172_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3171_, v_sz_3192_, v___x_3193_, v_x_3177_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = l_Lean_mkAppN(v_f_3186_, v_a_3195_);
lean_dec(v_a_3195_);
v___x_3197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3172_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3171_, v___x_3196_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3197_;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_f_3186_);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3172_);
v_a_3198_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3194_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3194_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_array_get_size(v_x_3177_);
lean_inc_ref(v_f_3186_);
v___x_3207_ = l_Lean_Meta_getFunInfoNArgs(v_f_3186_, v___x_3206_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_paramInfo_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v_paramInfo_3209_ = lean_ctor_get(v_a_3208_, 0);
lean_inc_ref(v_paramInfo_3209_);
lean_dec(v_a_3208_);
v___x_3210_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3173_);
lean_inc_ref(v_pre_3172_);
v___x_3211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3206_, v_paramInfo_3209_, v_pre_3172_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3171_, v___x_3210_, v_x_3177_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec_ref(v_paramInfo_3209_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l_Lean_mkAppN(v_f_3186_, v_a_3212_);
lean_dec(v_a_3212_);
v___x_3214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3172_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3171_, v___x_3213_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3214_;
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_f_3186_);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3172_);
v_a_3215_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v_f_3186_);
lean_dec_ref(v_x_3177_);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3172_);
v_a_3223_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3207_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3207_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
v___jp_3231_:
{
lean_object* v___x_3232_; 
lean_inc_ref(v_post_3173_);
lean_inc_ref(v_pre_3172_);
v___x_3232_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3172_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3171_, v_x_3176_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v_f_3186_ = v_a_3233_;
v___y_3187_ = v___y_3179_;
v___y_3188_ = v___y_3180_;
v___y_3189_ = v___y_3181_;
v___y_3190_ = v___y_3182_;
v___y_3191_ = v___y_3183_;
goto v___jp_3185_;
}
else
{
lean_dec_ref(v_x_3177_);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3172_);
return v___x_3232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3241_, lean_object* v_pre_3242_, lean_object* v_e_3243_, lean_object* v_post_3244_, uint8_t v_usedLetOnly_3245_, uint8_t v_skipConstInApp_3246_, uint8_t v_skipInstances_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_Core_checkSystem(v___x_3241_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3254_, 1);
lean_inc_ref(v_pre_3242_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3251_);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc_ref(v_e_3243_);
v___x_3255_ = lean_apply_6(v_pre_3242_, v_e_3243_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, lean_box(0));
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3304_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3304_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3304_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___y_3261_; 
switch(lean_obj_tag(v_a_3256_))
{
case 0:
{
lean_object* v_e_3296_; lean_object* v___x_3298_; 
lean_dec_ref(v_post_3244_);
lean_dec_ref(v_e_3243_);
lean_dec_ref(v_pre_3242_);
v_e_3296_ = lean_ctor_get(v_a_3256_, 0);
lean_inc_ref(v_e_3296_);
lean_dec_ref_known(v_a_3256_, 1);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v_e_3296_);
v___x_3298_ = v___x_3258_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_e_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
case 1:
{
lean_object* v_e_3300_; lean_object* v___x_3301_; 
lean_del_object(v___x_3258_);
lean_dec_ref(v_e_3243_);
v_e_3300_ = lean_ctor_get(v_a_3256_, 0);
lean_inc_ref(v_e_3300_);
lean_dec_ref_known(v_a_3256_, 1);
v___x_3301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v_e_3300_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3301_;
}
default: 
{
lean_object* v_e_x3f_3302_; 
lean_del_object(v___x_3258_);
v_e_x3f_3302_ = lean_ctor_get(v_a_3256_, 0);
lean_inc(v_e_x3f_3302_);
lean_dec_ref_known(v_a_3256_, 1);
if (lean_obj_tag(v_e_x3f_3302_) == 0)
{
v___y_3261_ = v_e_3243_;
goto v___jp_3260_;
}
else
{
lean_object* v_val_3303_; 
lean_dec_ref(v_e_3243_);
v_val_3303_ = lean_ctor_get(v_e_x3f_3302_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v_e_x3f_3302_, 1);
v___y_3261_ = v_val_3303_;
goto v___jp_3260_;
}
}
}
v___jp_3260_:
{
switch(lean_obj_tag(v___y_3261_))
{
case 7:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___x_3262_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3263_;
}
case 6:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___x_3264_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3265_;
}
case 8:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___x_3266_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3267_;
}
case 5:
{
lean_object* v_dummy_3268_; lean_object* v_nargs_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_dummy_3268_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3269_ = l_Lean_Expr_getAppNumArgs(v___y_3261_);
lean_inc(v_nargs_3269_);
v___x_3270_ = lean_mk_array(v_nargs_3269_, v_dummy_3268_);
v___x_3271_ = lean_unsigned_to_nat(1u);
v___x_3272_ = lean_nat_sub(v_nargs_3269_, v___x_3271_);
lean_dec(v_nargs_3269_);
v___x_3273_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3247_, v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v___y_3261_, v___x_3270_, v___x_3272_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3273_;
}
case 10:
{
lean_object* v_data_3274_; lean_object* v_expr_3275_; lean_object* v___x_3276_; 
v_data_3274_ = lean_ctor_get(v___y_3261_, 0);
v_expr_3275_ = lean_ctor_get(v___y_3261_, 1);
lean_inc_ref(v_expr_3275_);
lean_inc_ref(v_post_3244_);
lean_inc_ref(v_pre_3242_);
v___x_3276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v_expr_3275_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; size_t v___x_3278_; size_t v___x_3279_; uint8_t v___x_3280_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_ptr_addr(v_expr_3275_);
v___x_3279_ = lean_ptr_addr(v_a_3277_);
v___x_3280_ = lean_usize_dec_eq(v___x_3278_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_inc(v_data_3274_);
lean_dec_ref_known(v___y_3261_, 2);
v___x_3281_ = l_Lean_Expr_mdata___override(v_data_3274_, v_a_3277_);
v___x_3282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___x_3281_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; 
lean_dec(v_a_3277_);
v___x_3283_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3283_;
}
}
else
{
lean_dec_ref_known(v___y_3261_, 2);
lean_dec_ref(v_post_3244_);
lean_dec_ref(v_pre_3242_);
return v___x_3276_;
}
}
case 11:
{
lean_object* v_typeName_3284_; lean_object* v_idx_3285_; lean_object* v_struct_3286_; lean_object* v___x_3287_; 
v_typeName_3284_ = lean_ctor_get(v___y_3261_, 0);
v_idx_3285_ = lean_ctor_get(v___y_3261_, 1);
v_struct_3286_ = lean_ctor_get(v___y_3261_, 2);
lean_inc_ref(v_struct_3286_);
lean_inc_ref(v_post_3244_);
lean_inc_ref(v_pre_3242_);
v___x_3287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v_struct_3286_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; size_t v___x_3289_; size_t v___x_3290_; uint8_t v___x_3291_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = lean_ptr_addr(v_struct_3286_);
v___x_3290_ = lean_ptr_addr(v_a_3288_);
v___x_3291_ = lean_usize_dec_eq(v___x_3289_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_inc(v_idx_3285_);
lean_inc(v_typeName_3284_);
lean_dec_ref_known(v___y_3261_, 3);
v___x_3292_ = l_Lean_Expr_proj___override(v_typeName_3284_, v_idx_3285_, v_a_3288_);
v___x_3293_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___x_3292_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3293_;
}
else
{
lean_object* v___x_3294_; 
lean_dec(v_a_3288_);
v___x_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3294_;
}
}
else
{
lean_dec_ref_known(v___y_3261_, 3);
lean_dec_ref(v_post_3244_);
lean_dec_ref(v_pre_3242_);
return v___x_3287_;
}
}
default: 
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3242_, v_post_3244_, v_usedLetOnly_3245_, v_skipConstInApp_3246_, v_skipInstances_3247_, v___y_3261_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
return v___x_3295_;
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref(v_post_3244_);
lean_dec_ref(v_e_3243_);
lean_dec_ref(v_pre_3242_);
v_a_3305_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3255_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3255_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v_post_3244_);
lean_dec_ref(v_e_3243_);
lean_dec_ref(v_pre_3242_);
v_a_3313_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3254_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3254_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3321_, lean_object* v_pre_3322_, lean_object* v_e_3323_, lean_object* v_post_3324_, lean_object* v_usedLetOnly_3325_, lean_object* v_skipConstInApp_3326_, lean_object* v_skipInstances_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v_usedLetOnly_boxed_3334_; uint8_t v_skipConstInApp_boxed_3335_; uint8_t v_skipInstances_boxed_3336_; lean_object* v_res_3337_; 
v_usedLetOnly_boxed_3334_ = lean_unbox(v_usedLetOnly_3325_);
v_skipConstInApp_boxed_3335_ = lean_unbox(v_skipConstInApp_3326_);
v_skipInstances_boxed_3336_ = lean_unbox(v_skipInstances_3327_);
v_res_3337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3321_, v_pre_3322_, v_e_3323_, v_post_3324_, v_usedLetOnly_boxed_3334_, v_skipConstInApp_boxed_3335_, v_skipInstances_boxed_3336_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3338_, lean_object* v_post_3339_, uint8_t v_usedLetOnly_3340_, uint8_t v_skipConstInApp_3341_, uint8_t v_skipInstances_3342_, lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_inc(v_a_3344_);
v___x_3350_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3350_, 0, lean_box(0));
lean_closure_set(v___x_3350_, 1, lean_box(0));
lean_closure_set(v___x_3350_, 2, v_a_3344_);
v___x_3351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3350_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3386_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3386_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3386_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3352_, v_e_3343_);
lean_dec(v_a_3352_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v___x_3362_; 
lean_del_object(v___x_3354_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3358_ = lean_box(v_usedLetOnly_3340_);
v___x_3359_ = lean_box(v_skipConstInApp_3341_);
v___x_3360_ = lean_box(v_skipInstances_3342_);
lean_inc_ref(v_e_3343_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3361_, 0, v___x_3357_);
lean_closure_set(v___f_3361_, 1, v_pre_3338_);
lean_closure_set(v___f_3361_, 2, v_e_3343_);
lean_closure_set(v___f_3361_, 3, v_post_3339_);
lean_closure_set(v___f_3361_, 4, v___x_3358_);
lean_closure_set(v___f_3361_, 5, v___x_3359_);
lean_closure_set(v___f_3361_, 6, v___x_3360_);
v___x_3362_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3361_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___f_3364_; lean_object* v___x_3365_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc_n(v_a_3363_, 2);
lean_dec_ref_known(v___x_3362_, 1);
lean_inc(v_a_3344_);
v___f_3364_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3364_, 0, v_a_3344_);
lean_closure_set(v___f_3364_, 1, v_e_3343_);
lean_closure_set(v___f_3364_, 2, v_a_3363_);
v___x_3365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3364_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; 
v_unused_3373_ = lean_ctor_get(v___x_3365_, 0);
lean_dec(v_unused_3373_);
v___x_3367_ = v___x_3365_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v___x_3365_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v_a_3363_);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3363_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_a_3363_);
v_a_3374_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3365_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3365_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_dec_ref(v_e_3343_);
return v___x_3362_;
}
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3384_; 
lean_dec_ref(v_e_3343_);
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
v_val_3382_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v___x_3356_, 1);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_val_3382_);
v___x_3384_ = v___x_3354_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_val_3382_);
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
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_e_3343_);
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
v_a_3387_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3351_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3351_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3395_, lean_object* v_pre_3396_, lean_object* v_post_3397_, lean_object* v_usedLetOnly_3398_, lean_object* v_skipConstInApp_3399_, lean_object* v_skipInstances_3400_, lean_object* v_body_3401_, lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
uint8_t v_usedLetOnly_boxed_3409_; uint8_t v_skipConstInApp_boxed_3410_; uint8_t v_skipInstances_boxed_3411_; lean_object* v_res_3412_; 
v_usedLetOnly_boxed_3409_ = lean_unbox(v_usedLetOnly_3398_);
v_skipConstInApp_boxed_3410_ = lean_unbox(v_skipConstInApp_3399_);
v_skipInstances_boxed_3411_ = lean_unbox(v_skipInstances_3400_);
v_res_3412_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3395_, v_pre_3396_, v_post_3397_, v_usedLetOnly_boxed_3409_, v_skipConstInApp_boxed_3410_, v_skipInstances_boxed_3411_, v_body_3401_, v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3413_, lean_object* v_post_3414_, uint8_t v_usedLetOnly_3415_, uint8_t v_skipConstInApp_3416_, uint8_t v_skipInstances_3417_, lean_object* v_fvars_3418_, lean_object* v_e_3419_, lean_object* v_a_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
if (lean_obj_tag(v_e_3419_) == 7)
{
lean_object* v_binderName_3426_; lean_object* v_binderType_3427_; lean_object* v_body_3428_; uint8_t v_binderInfo_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_binderName_3426_ = lean_ctor_get(v_e_3419_, 0);
lean_inc(v_binderName_3426_);
v_binderType_3427_ = lean_ctor_get(v_e_3419_, 1);
lean_inc_ref(v_binderType_3427_);
v_body_3428_ = lean_ctor_get(v_e_3419_, 2);
lean_inc_ref(v_body_3428_);
v_binderInfo_3429_ = lean_ctor_get_uint8(v_e_3419_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3419_, 3);
v___x_3430_ = lean_expr_instantiate_rev(v_binderType_3427_, v_fvars_3418_);
lean_dec_ref(v_binderType_3427_);
lean_inc_ref(v_post_3414_);
lean_inc_ref(v_pre_3413_);
v___x_3431_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3413_, v_post_3414_, v_usedLetOnly_3415_, v_skipConstInApp_3416_, v_skipInstances_3417_, v___x_3430_, v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___f_3436_; uint8_t v___x_3437_; lean_object* v___x_3438_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = lean_box(v_usedLetOnly_3415_);
v___x_3434_ = lean_box(v_skipConstInApp_3416_);
v___x_3435_ = lean_box(v_skipInstances_3417_);
v___f_3436_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3436_, 0, v_fvars_3418_);
lean_closure_set(v___f_3436_, 1, v_pre_3413_);
lean_closure_set(v___f_3436_, 2, v_post_3414_);
lean_closure_set(v___f_3436_, 3, v___x_3433_);
lean_closure_set(v___f_3436_, 4, v___x_3434_);
lean_closure_set(v___f_3436_, 5, v___x_3435_);
lean_closure_set(v___f_3436_, 6, v_body_3428_);
v___x_3437_ = 0;
v___x_3438_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3426_, v_binderInfo_3429_, v_a_3432_, v___f_3436_, v___x_3437_, v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3438_;
}
else
{
lean_dec_ref(v_body_3428_);
lean_dec(v_binderName_3426_);
lean_dec_ref(v_fvars_3418_);
lean_dec_ref(v_post_3414_);
lean_dec_ref(v_pre_3413_);
return v___x_3431_;
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = lean_expr_instantiate_rev(v_e_3419_, v_fvars_3418_);
lean_dec_ref(v_e_3419_);
lean_inc_ref(v_post_3414_);
lean_inc_ref(v_pre_3413_);
v___x_3440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3413_, v_post_3414_, v_usedLetOnly_3415_, v_skipConstInApp_3416_, v_skipInstances_3417_, v___x_3439_, v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; uint8_t v___x_3442_; uint8_t v___x_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = 0;
v___x_3443_ = 1;
v___x_3444_ = 1;
v___x_3445_ = l_Lean_Meta_mkForallFVars(v_fvars_3418_, v_a_3441_, v___x_3442_, v_usedLetOnly_3415_, v___x_3443_, v___x_3444_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec_ref(v_fvars_3418_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___x_3447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3413_, v_post_3414_, v_usedLetOnly_3415_, v_skipConstInApp_3416_, v_skipInstances_3417_, v_a_3446_, v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3447_;
}
else
{
lean_dec_ref(v_post_3414_);
lean_dec_ref(v_pre_3413_);
return v___x_3445_;
}
}
else
{
lean_dec_ref(v_fvars_3418_);
lean_dec_ref(v_post_3414_);
lean_dec_ref(v_pre_3413_);
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3448_, lean_object* v_pre_3449_, lean_object* v_post_3450_, uint8_t v_usedLetOnly_3451_, uint8_t v_skipConstInApp_3452_, uint8_t v_skipInstances_3453_, lean_object* v_body_3454_, lean_object* v_x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_array_push(v_fvars_3448_, v_x_3455_);
v___x_3463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3449_, v_post_3450_, v_usedLetOnly_3451_, v_skipConstInApp_3452_, v_skipInstances_3453_, v___x_3462_, v_body_3454_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3464_, lean_object* v_post_3465_, lean_object* v_usedLetOnly_3466_, lean_object* v_skipConstInApp_3467_, lean_object* v_skipInstances_3468_, lean_object* v_e_3469_, lean_object* v_a_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
uint8_t v_usedLetOnly_boxed_3476_; uint8_t v_skipConstInApp_boxed_3477_; uint8_t v_skipInstances_boxed_3478_; lean_object* v_res_3479_; 
v_usedLetOnly_boxed_3476_ = lean_unbox(v_usedLetOnly_3466_);
v_skipConstInApp_boxed_3477_ = lean_unbox(v_skipConstInApp_3467_);
v_skipInstances_boxed_3478_ = lean_unbox(v_skipInstances_3468_);
v_res_3479_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3464_, v_post_3465_, v_usedLetOnly_boxed_3476_, v_skipConstInApp_boxed_3477_, v_skipInstances_boxed_3478_, v_e_3469_, v_a_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v_a_3470_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3480_, lean_object* v_post_3481_, lean_object* v_usedLetOnly_3482_, lean_object* v_skipConstInApp_3483_, lean_object* v_skipInstances_3484_, lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_bs_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
uint8_t v_usedLetOnly_boxed_3494_; uint8_t v_skipConstInApp_boxed_3495_; uint8_t v_skipInstances_boxed_3496_; size_t v_sz_boxed_3497_; size_t v_i_boxed_3498_; lean_object* v_res_3499_; 
v_usedLetOnly_boxed_3494_ = lean_unbox(v_usedLetOnly_3482_);
v_skipConstInApp_boxed_3495_ = lean_unbox(v_skipConstInApp_3483_);
v_skipInstances_boxed_3496_ = lean_unbox(v_skipInstances_3484_);
v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3498_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3480_, v_post_3481_, v_usedLetOnly_boxed_3494_, v_skipConstInApp_boxed_3495_, v_skipInstances_boxed_3496_, v_sz_boxed_3497_, v_i_boxed_3498_, v_bs_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3500_, lean_object* v_post_3501_, lean_object* v_usedLetOnly_3502_, lean_object* v_skipConstInApp_3503_, lean_object* v_skipInstances_3504_, lean_object* v_e_3505_, lean_object* v_a_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
uint8_t v_usedLetOnly_boxed_3512_; uint8_t v_skipConstInApp_boxed_3513_; uint8_t v_skipInstances_boxed_3514_; lean_object* v_res_3515_; 
v_usedLetOnly_boxed_3512_ = lean_unbox(v_usedLetOnly_3502_);
v_skipConstInApp_boxed_3513_ = lean_unbox(v_skipConstInApp_3503_);
v_skipInstances_boxed_3514_ = lean_unbox(v_skipInstances_3504_);
v_res_3515_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3500_, v_post_3501_, v_usedLetOnly_boxed_3512_, v_skipConstInApp_boxed_3513_, v_skipInstances_boxed_3514_, v_e_3505_, v_a_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v_a_3506_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3516_, lean_object* v_post_3517_, lean_object* v_usedLetOnly_3518_, lean_object* v_skipConstInApp_3519_, lean_object* v_skipInstances_3520_, lean_object* v_fvars_3521_, lean_object* v_e_3522_, lean_object* v_a_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
uint8_t v_usedLetOnly_boxed_3529_; uint8_t v_skipConstInApp_boxed_3530_; uint8_t v_skipInstances_boxed_3531_; lean_object* v_res_3532_; 
v_usedLetOnly_boxed_3529_ = lean_unbox(v_usedLetOnly_3518_);
v_skipConstInApp_boxed_3530_ = lean_unbox(v_skipConstInApp_3519_);
v_skipInstances_boxed_3531_ = lean_unbox(v_skipInstances_3520_);
v_res_3532_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3516_, v_post_3517_, v_usedLetOnly_boxed_3529_, v_skipConstInApp_boxed_3530_, v_skipInstances_boxed_3531_, v_fvars_3521_, v_e_3522_, v_a_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v_a_3523_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3533_, lean_object* v_post_3534_, lean_object* v_usedLetOnly_3535_, lean_object* v_skipConstInApp_3536_, lean_object* v_skipInstances_3537_, lean_object* v_fvars_3538_, lean_object* v_e_3539_, lean_object* v_a_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v_usedLetOnly_boxed_3546_; uint8_t v_skipConstInApp_boxed_3547_; uint8_t v_skipInstances_boxed_3548_; lean_object* v_res_3549_; 
v_usedLetOnly_boxed_3546_ = lean_unbox(v_usedLetOnly_3535_);
v_skipConstInApp_boxed_3547_ = lean_unbox(v_skipConstInApp_3536_);
v_skipInstances_boxed_3548_ = lean_unbox(v_skipInstances_3537_);
v_res_3549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3533_, v_post_3534_, v_usedLetOnly_boxed_3546_, v_skipConstInApp_boxed_3547_, v_skipInstances_boxed_3548_, v_fvars_3538_, v_e_3539_, v_a_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v_a_3540_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3550_, lean_object* v_post_3551_, lean_object* v_usedLetOnly_3552_, lean_object* v_skipConstInApp_3553_, lean_object* v_skipInstances_3554_, lean_object* v_fvars_3555_, lean_object* v_e_3556_, lean_object* v_a_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_usedLetOnly_boxed_3563_; uint8_t v_skipConstInApp_boxed_3564_; uint8_t v_skipInstances_boxed_3565_; lean_object* v_res_3566_; 
v_usedLetOnly_boxed_3563_ = lean_unbox(v_usedLetOnly_3552_);
v_skipConstInApp_boxed_3564_ = lean_unbox(v_skipConstInApp_3553_);
v_skipInstances_boxed_3565_ = lean_unbox(v_skipInstances_3554_);
v_res_3566_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3550_, v_post_3551_, v_usedLetOnly_boxed_3563_, v_skipConstInApp_boxed_3564_, v_skipInstances_boxed_3565_, v_fvars_3555_, v_e_3556_, v_a_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v_a_3557_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3567_, lean_object* v___x_3568_, lean_object* v_pre_3569_, lean_object* v_post_3570_, lean_object* v_usedLetOnly_3571_, lean_object* v_skipConstInApp_3572_, lean_object* v_skipInstances_3573_, lean_object* v_a_3574_, lean_object* v_b_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
uint8_t v_usedLetOnly_boxed_3582_; uint8_t v_skipConstInApp_boxed_3583_; uint8_t v_skipInstances_boxed_3584_; lean_object* v_res_3585_; 
v_usedLetOnly_boxed_3582_ = lean_unbox(v_usedLetOnly_3571_);
v_skipConstInApp_boxed_3583_ = lean_unbox(v_skipConstInApp_3572_);
v_skipInstances_boxed_3584_ = lean_unbox(v_skipInstances_3573_);
v_res_3585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3567_, v___x_3568_, v_pre_3569_, v_post_3570_, v_usedLetOnly_boxed_3582_, v_skipConstInApp_boxed_3583_, v_skipInstances_boxed_3584_, v_a_3574_, v_b_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___x_3568_);
lean_dec(v_upperBound_3567_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3586_, lean_object* v_pre_3587_, lean_object* v_post_3588_, lean_object* v_usedLetOnly_3589_, lean_object* v_skipConstInApp_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
uint8_t v_skipInstances_boxed_3600_; uint8_t v_usedLetOnly_boxed_3601_; uint8_t v_skipConstInApp_boxed_3602_; lean_object* v_res_3603_; 
v_skipInstances_boxed_3600_ = lean_unbox(v_skipInstances_3586_);
v_usedLetOnly_boxed_3601_ = lean_unbox(v_usedLetOnly_3589_);
v_skipConstInApp_boxed_3602_ = lean_unbox(v_skipConstInApp_3590_);
v_res_3603_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3600_, v_pre_3587_, v_post_3588_, v_usedLetOnly_boxed_3601_, v_skipConstInApp_boxed_3602_, v_x_3591_, v_x_3592_, v_x_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
return v_res_3603_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_3604_; lean_object* v___x_3605_; 
v_cellCount_3604_ = lean_unsigned_to_nat(16u);
v___x_3605_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3604_);
return v___x_3605_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v_cellCount_3606_; lean_object* v___x_3607_; 
v_cellCount_3606_ = lean_unsigned_to_nat(16u);
v___x_3607_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3608_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3609_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v___x_3609_);
lean_ctor_set(v___x_3611_, 2, v___x_3608_);
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3613_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3613_, 0, lean_box(0));
lean_closure_set(v___x_3613_, 1, lean_box(0));
lean_closure_set(v___x_3613_, 2, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3614_, lean_object* v_pre_3615_, lean_object* v_post_3616_, uint8_t v_usedLetOnly_3617_, uint8_t v_skipConstInApp_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v_a_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3624_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3);
v___x_3625_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3624_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v___x_3625_);
v___x_3627_ = 0;
v___x_3628_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3615_, v_post_3616_, v_usedLetOnly_3617_, v_skipConstInApp_3618_, v___x_3627_, v_input_3614_, v_a_3626_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3630_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3630_, 0, lean_box(0));
lean_closure_set(v___x_3630_, 1, lean_box(0));
lean_closure_set(v___x_3630_, 2, v_a_3626_);
v___x_3631_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3630_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v___x_3631_, 0);
lean_dec(v_unused_3639_);
v___x_3633_ = v___x_3631_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_dec(v___x_3631_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v_a_3629_);
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3629_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
else
{
lean_dec(v_a_3626_);
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3640_, lean_object* v_pre_3641_, lean_object* v_post_3642_, lean_object* v_usedLetOnly_3643_, lean_object* v_skipConstInApp_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
uint8_t v_usedLetOnly_boxed_3650_; uint8_t v_skipConstInApp_boxed_3651_; lean_object* v_res_3652_; 
v_usedLetOnly_boxed_3650_ = lean_unbox(v_usedLetOnly_3643_);
v_skipConstInApp_boxed_3651_ = lean_unbox(v_skipConstInApp_3644_);
v_res_3652_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3640_, v_pre_3641_, v_post_3642_, v_usedLetOnly_boxed_3650_, v_skipConstInApp_boxed_3651_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3654_, lean_object* v_p_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3661_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3654_, v_a_3657_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___f_3663_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3664_, 0, v_p_3655_);
v___x_3665_ = 0;
v___x_3666_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3662_, v___f_3663_, v___f_3664_, v___x_3665_, v___x_3665_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3667_, lean_object* v_p_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_etaStructReduce(v_e_3667_, v_p_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3675_, lean_object* v___x_3676_, lean_object* v_pre_3677_, lean_object* v_post_3678_, uint8_t v_usedLetOnly_3679_, uint8_t v_skipConstInApp_3680_, uint8_t v_skipInstances_3681_, lean_object* v___x_3682_, lean_object* v_inst_3683_, lean_object* v_R_3684_, lean_object* v_a_3685_, lean_object* v_b_3686_, lean_object* v_c_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3675_, v___x_3676_, v_pre_3677_, v_post_3678_, v_usedLetOnly_3679_, v_skipConstInApp_3680_, v_skipInstances_3681_, v_a_3685_, v_b_3686_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3695_ = _args[0];
lean_object* v___x_3696_ = _args[1];
lean_object* v_pre_3697_ = _args[2];
lean_object* v_post_3698_ = _args[3];
lean_object* v_usedLetOnly_3699_ = _args[4];
lean_object* v_skipConstInApp_3700_ = _args[5];
lean_object* v_skipInstances_3701_ = _args[6];
lean_object* v___x_3702_ = _args[7];
lean_object* v_inst_3703_ = _args[8];
lean_object* v_R_3704_ = _args[9];
lean_object* v_a_3705_ = _args[10];
lean_object* v_b_3706_ = _args[11];
lean_object* v_c_3707_ = _args[12];
lean_object* v___y_3708_ = _args[13];
lean_object* v___y_3709_ = _args[14];
lean_object* v___y_3710_ = _args[15];
lean_object* v___y_3711_ = _args[16];
lean_object* v___y_3712_ = _args[17];
lean_object* v___y_3713_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3714_; uint8_t v_skipConstInApp_boxed_3715_; uint8_t v_skipInstances_boxed_3716_; lean_object* v_res_3717_; 
v_usedLetOnly_boxed_3714_ = lean_unbox(v_usedLetOnly_3699_);
v_skipConstInApp_boxed_3715_ = lean_unbox(v_skipConstInApp_3700_);
v_skipInstances_boxed_3716_ = lean_unbox(v_skipInstances_3701_);
v_res_3717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3695_, v___x_3696_, v_pre_3697_, v_post_3698_, v_usedLetOnly_boxed_3714_, v_skipConstInApp_boxed_3715_, v_skipInstances_boxed_3716_, v___x_3702_, v_inst_3703_, v_R_3704_, v_a_3705_, v_b_3706_, v_c_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec(v___x_3702_);
lean_dec_ref(v___x_3696_);
lean_dec(v_upperBound_3695_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3718_, lean_object* v_m_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3719_, v_a_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3722_, lean_object* v_m_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3722_, v_m_3723_, v_a_3724_);
lean_dec_ref(v_a_3724_);
lean_dec_ref(v_m_3723_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3726_, lean_object* v_name_3727_, uint8_t v_bi_3728_, lean_object* v_type_3729_, lean_object* v_k_3730_, uint8_t v_kind_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3727_, v_bi_3728_, v_type_3729_, v_k_3730_, v_kind_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_name_3740_, lean_object* v_bi_3741_, lean_object* v_type_3742_, lean_object* v_k_3743_, lean_object* v_kind_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
uint8_t v_bi_boxed_3751_; uint8_t v_kind_boxed_3752_; lean_object* v_res_3753_; 
v_bi_boxed_3751_ = lean_unbox(v_bi_3741_);
v_kind_boxed_3752_ = lean_unbox(v_kind_3744_);
v_res_3753_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3739_, v_name_3740_, v_bi_boxed_3751_, v_type_3742_, v_k_3743_, v_kind_boxed_3752_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3754_, lean_object* v_name_3755_, lean_object* v_type_3756_, lean_object* v_val_3757_, lean_object* v_k_3758_, uint8_t v_nondep_3759_, uint8_t v_kind_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3755_, v_type_3756_, v_val_3757_, v_k_3758_, v_nondep_3759_, v_kind_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_name_3769_, lean_object* v_type_3770_, lean_object* v_val_3771_, lean_object* v_k_3772_, lean_object* v_nondep_3773_, lean_object* v_kind_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
uint8_t v_nondep_boxed_3781_; uint8_t v_kind_boxed_3782_; lean_object* v_res_3783_; 
v_nondep_boxed_3781_ = lean_unbox(v_nondep_3773_);
v_kind_boxed_3782_ = lean_unbox(v_kind_3774_);
v_res_3783_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3768_, v_name_3769_, v_type_3770_, v_val_3771_, v_k_3772_, v_nondep_boxed_3781_, v_kind_boxed_3782_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3784_, lean_object* v_ref_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3785_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_ref_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3792_, v_ref_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_x_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3809_, v_x_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3818_, lean_object* v_m_3819_, lean_object* v_query_3820_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3819_, v_query_3820_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___boxed(lean_object* v_00_u03b2_3822_, lean_object* v_m_3823_, lean_object* v_query_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(v_00_u03b2_3822_, v_m_3823_, v_query_3824_);
lean_dec_ref(v_query_3824_);
lean_dec_ref(v_m_3823_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12(lean_object* v_00_u03b2_3826_, lean_object* v_m_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___redArg(v_m_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12___boxed(lean_object* v_00_u03b2_3829_, lean_object* v_m_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12(v_00_u03b2_3829_, v_m_3830_);
lean_dec_ref(v_m_3830_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3832_, lean_object* v_m_3833_, lean_object* v_query_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_m_3833_, v_query_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3836_, lean_object* v_m_3837_, lean_object* v_query_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3836_, v_m_3837_, v_query_3838_);
lean_dec_ref(v_query_3838_);
lean_dec_ref(v_m_3837_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3840_, lean_object* v_m_3841_, lean_object* v_query_3842_, lean_object* v_x_3843_, lean_object* v_x_3844_, lean_object* v_x_3845_, lean_object* v_x_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_m_3841_, v_query_3842_, v_x_3843_, v_x_3844_, v_x_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3848_, lean_object* v_m_3849_, lean_object* v_query_3850_, lean_object* v_x_3851_, lean_object* v_x_3852_, lean_object* v_x_3853_, lean_object* v_x_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3848_, v_m_3849_, v_query_3850_, v_x_3851_, v_x_3852_, v_x_3853_, v_x_3854_);
lean_dec_ref(v_query_3850_);
lean_dec_ref(v_m_3849_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18(lean_object* v_00_u03b2_3856_, lean_object* v_init_3857_, lean_object* v_b_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___redArg(v_init_3857_, v_b_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18___boxed(lean_object* v_00_u03b2_3860_, lean_object* v_init_3861_, lean_object* v_b_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18(v_00_u03b2_3860_, v_init_3861_, v_b_3862_);
lean_dec_ref(v_b_3862_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19(lean_object* v_00_u03b2_3864_, lean_object* v_b_3865_, lean_object* v_acc_3866_, lean_object* v_i_3867_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___redArg(v_b_3865_, v_acc_3866_, v_i_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19___boxed(lean_object* v_00_u03b2_3869_, lean_object* v_b_3870_, lean_object* v_acc_3871_, lean_object* v_i_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__12_spec__18_spec__19(v_00_u03b2_3869_, v_b_3870_, v_acc_3871_, v_i_3872_);
lean_dec_ref(v_b_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3874_, lean_object* v_inst_3875_, lean_object* v_toBind_3876_, lean_object* v___f_3877_, lean_object* v_____do__lift_3878_){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3879_, 0, v_____do__lift_3878_);
lean_closure_set(v___x_3879_, 1, v_binderType_3874_);
v___x_3880_ = lean_apply_2(v_inst_3875_, lean_box(0), v___x_3879_);
v___x_3881_ = lean_apply_4(v_toBind_3876_, lean_box(0), lean_box(0), v___x_3880_, v___f_3877_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3882_, lean_object* v_usedFields_3883_, lean_object* v_binderName_3884_, lean_object* v_body_3885_, lean_object* v_val_3886_, lean_object* v_inst_3887_, lean_object* v_inst_3888_, lean_object* v_fieldVal_x3f_3889_, lean_object* v_____do__lift_3890_){
_start:
{
uint8_t v_____do__lift_469__boxed_3891_; lean_object* v_res_3892_; 
v_____do__lift_469__boxed_3891_ = lean_unbox(v_____do__lift_3890_);
v_res_3892_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3882_, v_usedFields_3883_, v_binderName_3884_, v_body_3885_, v_val_3886_, v_inst_3887_, v_inst_3888_, v_fieldVal_x3f_3889_, v_____do__lift_469__boxed_3891_);
lean_dec_ref(v_val_3886_);
lean_dec_ref(v_body_3885_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3893_, lean_object* v_usedFields_3894_, lean_object* v_binderName_3895_, lean_object* v_body_3896_, lean_object* v_inst_3897_, lean_object* v_inst_3898_, lean_object* v_fieldVal_x3f_3899_, lean_object* v_binderType_3900_, lean_object* v_toBind_3901_, lean_object* v_____x_3902_){
_start:
{
if (lean_obj_tag(v_____x_3902_) == 1)
{
lean_object* v_val_3903_; lean_object* v___f_3904_; lean_object* v___f_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_val_3903_ = lean_ctor_get(v_____x_3902_, 0);
lean_inc_n(v_val_3903_, 2);
lean_dec_ref_known(v_____x_3902_, 1);
lean_inc_n(v_inst_3898_, 2);
v___f_3904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3904_, 0, v_toPure_3893_);
lean_closure_set(v___f_3904_, 1, v_usedFields_3894_);
lean_closure_set(v___f_3904_, 2, v_binderName_3895_);
lean_closure_set(v___f_3904_, 3, v_body_3896_);
lean_closure_set(v___f_3904_, 4, v_val_3903_);
lean_closure_set(v___f_3904_, 5, v_inst_3897_);
lean_closure_set(v___f_3904_, 6, v_inst_3898_);
lean_closure_set(v___f_3904_, 7, v_fieldVal_x3f_3899_);
lean_inc(v_toBind_3901_);
v___f_3905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3905_, 0, v_binderType_3900_);
lean_closure_set(v___f_3905_, 1, v_inst_3898_);
lean_closure_set(v___f_3905_, 2, v_toBind_3901_);
lean_closure_set(v___f_3905_, 3, v___f_3904_);
v___x_3906_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3906_, 0, v_val_3903_);
v___x_3907_ = lean_apply_2(v_inst_3898_, lean_box(0), v___x_3906_);
v___x_3908_ = lean_apply_4(v_toBind_3901_, lean_box(0), lean_box(0), v___x_3907_, v___f_3905_);
return v___x_3908_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v_____x_3902_);
lean_dec(v_toBind_3901_);
lean_dec_ref(v_binderType_3900_);
lean_dec(v_fieldVal_x3f_3899_);
lean_dec(v_inst_3898_);
lean_dec_ref(v_inst_3897_);
lean_dec_ref(v_body_3896_);
lean_dec(v_binderName_3895_);
lean_dec(v_usedFields_3894_);
v___x_3909_ = lean_box(0);
v___x_3910_ = lean_apply_2(v_toPure_3893_, lean_box(0), v___x_3909_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3914_, lean_object* v_inst_3915_, lean_object* v_fieldVal_x3f_3916_, lean_object* v_usedFields_3917_, lean_object* v_e_3918_){
_start:
{
lean_object* v_toApplicative_3919_; lean_object* v_toBind_3920_; lean_object* v_toPure_3921_; 
v_toApplicative_3919_ = lean_ctor_get(v_inst_3914_, 0);
v_toBind_3920_ = lean_ctor_get(v_inst_3914_, 1);
v_toPure_3921_ = lean_ctor_get(v_toApplicative_3919_, 1);
lean_inc(v_toPure_3921_);
if (lean_obj_tag(v_e_3918_) == 6)
{
lean_object* v_binderName_3926_; lean_object* v_binderType_3927_; lean_object* v_body_3928_; lean_object* v___f_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_inc_n(v_toBind_3920_, 2);
v_binderName_3926_ = lean_ctor_get(v_e_3918_, 0);
lean_inc_n(v_binderName_3926_, 2);
v_binderType_3927_ = lean_ctor_get(v_e_3918_, 1);
lean_inc_ref(v_binderType_3927_);
v_body_3928_ = lean_ctor_get(v_e_3918_, 2);
lean_inc_ref(v_body_3928_);
lean_dec_ref_known(v_e_3918_, 3);
lean_inc(v_fieldVal_x3f_3916_);
v___f_3929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3929_, 0, v_toPure_3921_);
lean_closure_set(v___f_3929_, 1, v_usedFields_3917_);
lean_closure_set(v___f_3929_, 2, v_binderName_3926_);
lean_closure_set(v___f_3929_, 3, v_body_3928_);
lean_closure_set(v___f_3929_, 4, v_inst_3914_);
lean_closure_set(v___f_3929_, 5, v_inst_3915_);
lean_closure_set(v___f_3929_, 6, v_fieldVal_x3f_3916_);
lean_closure_set(v___f_3929_, 7, v_binderType_3927_);
lean_closure_set(v___f_3929_, 8, v_toBind_3920_);
v___x_3930_ = lean_apply_1(v_fieldVal_x3f_3916_, v_binderName_3926_);
v___x_3931_ = lean_apply_4(v_toBind_3920_, lean_box(0), lean_box(0), v___x_3930_, v___f_3929_);
return v___x_3931_;
}
else
{
lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_fieldVal_x3f_3916_);
lean_dec(v_inst_3915_);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_inst_3914_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3949_ = lean_ctor_get(v_inst_3914_, 1);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_inst_3914_, 0);
lean_dec(v_unused_3950_);
v___x_3933_ = v_inst_3914_;
v_isShared_3934_ = v_isSharedCheck_3948_;
goto v_resetjp_3932_;
}
else
{
lean_dec(v_inst_3914_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3948_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
lean_inc_ref(v_e_3918_);
v___x_3935_ = l_Lean_Expr_cleanupAnnotations(v_e_3918_);
v___x_3936_ = l_Lean_Expr_isApp(v___x_3935_);
if (v___x_3936_ == 0)
{
lean_dec_ref(v___x_3935_);
lean_del_object(v___x_3933_);
goto v___jp_3922_;
}
else
{
lean_object* v_arg_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_arg_3937_ = lean_ctor_get(v___x_3935_, 1);
lean_inc_ref(v_arg_3937_);
v___x_3938_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3935_);
v___x_3939_ = l_Lean_Expr_isApp(v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec_ref(v___x_3938_);
lean_dec_ref(v_arg_3937_);
lean_del_object(v___x_3933_);
goto v___jp_3922_;
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3938_);
v___x_3941_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3942_ = l_Lean_Expr_isConstOf(v___x_3940_, v___x_3941_);
lean_dec_ref(v___x_3940_);
if (v___x_3942_ == 0)
{
lean_dec_ref(v_arg_3937_);
lean_del_object(v___x_3933_);
goto v___jp_3922_;
}
else
{
lean_object* v___x_3944_; 
lean_dec_ref(v_e_3918_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_arg_3937_);
lean_ctor_set(v___x_3933_, 0, v_usedFields_3917_);
v___x_3944_ = v___x_3933_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_usedFields_3917_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_arg_3937_);
v___x_3944_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___x_3946_ = lean_apply_2(v_toPure_3921_, lean_box(0), v___x_3945_);
return v___x_3946_;
}
}
}
}
}
}
v___jp_3922_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v_usedFields_3917_);
lean_ctor_set(v___x_3923_, 1, v_e_3918_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v___x_3925_ = lean_apply_2(v_toPure_3921_, lean_box(0), v___x_3924_);
return v___x_3925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3951_, lean_object* v_usedFields_3952_, lean_object* v_binderName_3953_, lean_object* v_body_3954_, lean_object* v_val_3955_, lean_object* v_inst_3956_, lean_object* v_inst_3957_, lean_object* v_fieldVal_x3f_3958_, uint8_t v_____do__lift_3959_){
_start:
{
if (v_____do__lift_3959_ == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec(v_fieldVal_x3f_3958_);
lean_dec(v_inst_3957_);
lean_dec_ref(v_inst_3956_);
lean_dec(v_binderName_3953_);
lean_dec(v_usedFields_3952_);
v___x_3960_ = lean_box(0);
v___x_3961_ = lean_apply_2(v_toPure_3951_, lean_box(0), v___x_3960_);
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec(v_toPure_3951_);
v___x_3962_ = l_Lean_NameSet_insert(v_usedFields_3952_, v_binderName_3953_);
v___x_3963_ = lean_expr_instantiate1(v_body_3954_, v_val_3955_);
v___x_3964_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3956_, v_inst_3957_, v_fieldVal_x3f_3958_, v___x_3962_, v___x_3963_);
return v___x_3964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3965_, lean_object* v_inst_3966_, lean_object* v_inst_3967_, lean_object* v_fieldVal_x3f_3968_, lean_object* v_usedFields_3969_, lean_object* v_e_3970_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3966_, v_inst_3967_, v_fieldVal_x3f_3968_, v_usedFields_3969_, v_e_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_fieldVal_x3f_3974_, lean_object* v_toPure_3975_, lean_object* v_____s_3976_){
_start:
{
lean_object* v_fst_3977_; 
v_fst_3977_ = lean_ctor_get(v_____s_3976_, 0);
if (lean_obj_tag(v_fst_3977_) == 0)
{
lean_object* v_snd_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_toPure_3975_);
v_snd_3978_ = lean_ctor_get(v_____s_3976_, 1);
lean_inc(v_snd_3978_);
lean_dec_ref(v_____s_3976_);
v___x_3979_ = l_Lean_NameSet_empty;
v___x_3980_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3972_, v_inst_3973_, v_fieldVal_x3f_3974_, v___x_3979_, v_snd_3978_);
return v___x_3980_;
}
else
{
lean_object* v_val_3981_; lean_object* v___x_3982_; 
lean_inc_ref(v_fst_3977_);
lean_dec_ref(v_____s_3976_);
lean_dec(v_fieldVal_x3f_3974_);
lean_dec(v_inst_3973_);
lean_dec_ref(v_inst_3972_);
v_val_3981_ = lean_ctor_get(v_fst_3977_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v_fst_3977_, 1);
v___x_3982_ = lean_apply_2(v_toPure_3975_, lean_box(0), v_val_3981_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3983_, lean_object* v_a_3984_, lean_object* v___x_3985_, lean_object* v_toPure_3986_, lean_object* v_____r_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = lean_expr_instantiate1(v_body_3983_, v_a_3984_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3985_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
v___x_3991_ = lean_apply_2(v_toPure_3986_, lean_box(0), v___x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3992_, lean_object* v_a_3993_, lean_object* v___x_3994_, lean_object* v_toPure_3995_, lean_object* v_____r_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3992_, v_a_3993_, v___x_3994_, v_toPure_3995_, v_____r_3996_);
lean_dec_ref(v_a_3993_);
lean_dec_ref(v_body_3992_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_4000_, lean_object* v_toPure_4001_, lean_object* v___f_4002_, uint8_t v_____do__lift_4003_){
_start:
{
if (v_____do__lift_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v___f_4002_);
v___x_4004_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_4005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v_snd_4000_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
v___x_4007_ = lean_apply_2(v_toPure_4001_, lean_box(0), v___x_4006_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v_toPure_4001_);
lean_dec(v_snd_4000_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_apply_1(v___f_4002_, v___x_4008_);
return v___x_4009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_4010_, lean_object* v_toPure_4011_, lean_object* v___f_4012_, lean_object* v_____do__lift_4013_){
_start:
{
uint8_t v_____do__lift_852__boxed_4014_; lean_object* v_res_4015_; 
v_____do__lift_852__boxed_4014_ = lean_unbox(v_____do__lift_4013_);
v_res_4015_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_4010_, v_toPure_4011_, v___f_4012_, v_____do__lift_852__boxed_4014_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_4016_, lean_object* v_inst_4017_, lean_object* v_toBind_4018_, lean_object* v___f_4019_, lean_object* v_____do__lift_4020_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_4021_, 0, v_____do__lift_4020_);
lean_closure_set(v___x_4021_, 1, v_binderType_4016_);
v___x_4022_ = lean_apply_2(v_inst_4017_, lean_box(0), v___x_4021_);
v___x_4023_ = lean_apply_4(v_toBind_4018_, lean_box(0), lean_box(0), v___x_4022_, v___f_4019_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_4024_, lean_object* v_toPure_4025_, lean_object* v_levels_x3f_4026_, uint8_t v___x_4027_, lean_object* v_inst_4028_, lean_object* v_toBind_4029_, lean_object* v_a_4030_, lean_object* v_x_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_snd_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4054_; 
v_snd_4033_ = lean_ctor_get(v___y_4032_, 1);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___y_4032_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; 
v_unused_4055_ = lean_ctor_get(v___y_4032_, 0);
lean_dec(v_unused_4055_);
v___x_4035_ = v___y_4032_;
v_isShared_4036_ = v_isSharedCheck_4054_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_snd_4033_);
lean_dec(v___y_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4054_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
if (lean_obj_tag(v_snd_4033_) == 6)
{
lean_object* v_binderType_4037_; lean_object* v_body_4038_; lean_object* v___f_4039_; 
lean_del_object(v___x_4035_);
v_binderType_4037_ = lean_ctor_get(v_snd_4033_, 1);
lean_inc_ref(v_binderType_4037_);
v_body_4038_ = lean_ctor_get(v_snd_4033_, 2);
lean_inc(v_toPure_4025_);
lean_inc(v___x_4024_);
lean_inc_ref(v_a_4030_);
lean_inc_ref(v_body_4038_);
v___f_4039_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_4039_, 0, v_body_4038_);
lean_closure_set(v___f_4039_, 1, v_a_4030_);
lean_closure_set(v___f_4039_, 2, v___x_4024_);
lean_closure_set(v___f_4039_, 3, v_toPure_4025_);
if (lean_obj_tag(v_levels_x3f_4026_) == 0)
{
if (v___x_4027_ == 0)
{
lean_inc_ref(v_body_4038_);
lean_dec_ref(v___f_4039_);
lean_dec_ref(v_binderType_4037_);
lean_dec_ref_known(v_snd_4033_, 3);
lean_dec(v_toBind_4029_);
lean_dec(v_inst_4028_);
goto v___jp_4040_;
}
else
{
lean_object* v___f_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec(v___x_4024_);
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4043_, 0, v_snd_4033_);
lean_closure_set(v___f_4043_, 1, v_toPure_4025_);
lean_closure_set(v___f_4043_, 2, v___f_4039_);
lean_inc(v_toBind_4029_);
lean_inc(v_inst_4028_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4044_, 0, v_binderType_4037_);
lean_closure_set(v___f_4044_, 1, v_inst_4028_);
lean_closure_set(v___f_4044_, 2, v_toBind_4029_);
lean_closure_set(v___f_4044_, 3, v___f_4043_);
v___x_4045_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_4045_, 0, v_a_4030_);
v___x_4046_ = lean_apply_2(v_inst_4028_, lean_box(0), v___x_4045_);
v___x_4047_ = lean_apply_4(v_toBind_4029_, lean_box(0), lean_box(0), v___x_4046_, v___f_4044_);
return v___x_4047_;
}
}
else
{
lean_inc_ref(v_body_4038_);
lean_dec_ref(v___f_4039_);
lean_dec_ref(v_binderType_4037_);
lean_dec_ref_known(v_snd_4033_, 3);
lean_dec(v_toBind_4029_);
lean_dec(v_inst_4028_);
goto v___jp_4040_;
}
v___jp_4040_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_box(0);
v___x_4042_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_4038_, v_a_4030_, v___x_4024_, v_toPure_4025_, v___x_4041_);
lean_dec_ref(v_a_4030_);
lean_dec_ref(v_body_4038_);
return v___x_4042_;
}
}
else
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
lean_dec_ref(v_a_4030_);
lean_dec(v_toBind_4029_);
lean_dec(v_inst_4028_);
lean_dec(v___x_4024_);
v___x_4048_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4048_);
v___x_4050_ = v___x_4035_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_snd_4033_);
v___x_4050_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
v___x_4052_ = lean_apply_2(v_toPure_4025_, lean_box(0), v___x_4051_);
return v___x_4052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_4056_, lean_object* v_toPure_4057_, lean_object* v_levels_x3f_4058_, lean_object* v___x_4059_, lean_object* v_inst_4060_, lean_object* v_toBind_4061_, lean_object* v_a_4062_, lean_object* v_x_4063_, lean_object* v___y_4064_){
_start:
{
uint8_t v___x_888__boxed_4065_; lean_object* v_res_4066_; 
v___x_888__boxed_4065_ = lean_unbox(v___x_4059_);
v_res_4066_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_4056_, v_toPure_4057_, v_levels_x3f_4058_, v___x_888__boxed_4065_, v_inst_4060_, v_toBind_4061_, v_a_4062_, v_x_4063_, v___y_4064_);
lean_dec(v_levels_x3f_4058_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_4067_, lean_object* v_levels_x3f_4068_, uint8_t v___x_4069_, lean_object* v_inst_4070_, lean_object* v_toBind_4071_, lean_object* v_params_4072_, lean_object* v_inst_4073_, lean_object* v___f_4074_, lean_object* v_val_4075_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___f_4078_; lean_object* v___x_4079_; size_t v_sz_4080_; size_t v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4076_ = lean_box(0);
v___x_4077_ = lean_box(v___x_4069_);
lean_inc(v_toBind_4071_);
v___f_4078_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_4078_, 0, v___x_4076_);
lean_closure_set(v___f_4078_, 1, v_toPure_4067_);
lean_closure_set(v___f_4078_, 2, v_levels_x3f_4068_);
lean_closure_set(v___f_4078_, 3, v___x_4077_);
lean_closure_set(v___f_4078_, 4, v_inst_4070_);
lean_closure_set(v___f_4078_, 5, v_toBind_4071_);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4076_);
lean_ctor_set(v___x_4079_, 1, v_val_4075_);
v_sz_4080_ = lean_array_size(v_params_4072_);
v___x_4081_ = ((size_t)0ULL);
v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4073_, v_params_4072_, v___f_4078_, v_sz_4080_, v___x_4081_, v___x_4079_);
v___x_4083_ = lean_apply_4(v_toBind_4071_, lean_box(0), lean_box(0), v___x_4082_, v___f_4074_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v_toPure_4084_, lean_object* v_levels_x3f_4085_, lean_object* v___x_4086_, lean_object* v_inst_4087_, lean_object* v_toBind_4088_, lean_object* v_params_4089_, lean_object* v_inst_4090_, lean_object* v___f_4091_, lean_object* v_val_4092_){
_start:
{
uint8_t v___x_950__boxed_4093_; lean_object* v_res_4094_; 
v___x_950__boxed_4093_ = lean_unbox(v___x_4086_);
v_res_4094_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v_toPure_4084_, v_levels_x3f_4085_, v___x_950__boxed_4093_, v_inst_4087_, v_toBind_4088_, v_params_4089_, v_inst_4090_, v___f_4091_, v_val_4092_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4095_, lean_object* v_us_4096_, uint8_t v___x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4095_, v_us_4096_, v___x_4097_, v___y_4100_, v___y_4101_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4104_, lean_object* v_us_4105_, lean_object* v___x_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v___x_976__boxed_4112_; lean_object* v_res_4113_; 
v___x_976__boxed_4112_ = lean_unbox(v___x_4106_);
v_res_4113_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4104_, v_us_4105_, v___x_976__boxed_4112_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec_ref(v_cinfo_4104_);
return v_res_4113_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4117_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4118_ = lean_unsigned_to_nat(2u);
v___x_4119_ = lean_unsigned_to_nat(202u);
v___x_4120_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4121_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4122_ = l_mkPanicMessageWithDecl(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_, v___x_4117_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4123_, lean_object* v_inst_4124_, lean_object* v_toPure_4125_, lean_object* v_levels_x3f_4126_, lean_object* v_inst_4127_, lean_object* v_toBind_4128_, lean_object* v_params_4129_, lean_object* v___f_4130_, lean_object* v_us_4131_){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4132_ = l_List_lengthTR___redArg(v_us_4131_);
v___x_4133_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4123_);
v___x_4134_ = l_List_lengthTR___redArg(v___x_4133_);
lean_dec(v___x_4133_);
v___x_4135_ = lean_nat_dec_eq(v___x_4132_, v___x_4134_);
lean_dec(v___x_4134_);
lean_dec(v___x_4132_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_dec(v_us_4131_);
lean_dec(v___f_4130_);
lean_dec_ref(v_params_4129_);
lean_dec(v_toBind_4128_);
lean_dec(v_inst_4127_);
lean_dec(v_levels_x3f_4126_);
lean_dec(v_toPure_4125_);
lean_dec_ref(v_cinfo_4123_);
v___x_4136_ = lean_box(0);
v___x_4137_ = l_instInhabitedOfMonad___redArg(v_inst_4124_, v___x_4136_);
v___x_4138_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4139_ = l_panic___redArg(v___x_4137_, v___x_4138_);
lean_dec(v___x_4137_);
return v___x_4139_;
}
else
{
lean_object* v___x_4140_; lean_object* v___f_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___f_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4140_ = lean_box(v___x_4135_);
lean_inc(v_toBind_4128_);
lean_inc(v_inst_4127_);
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_4141_, 0, v_toPure_4125_);
lean_closure_set(v___f_4141_, 1, v_levels_x3f_4126_);
lean_closure_set(v___f_4141_, 2, v___x_4140_);
lean_closure_set(v___f_4141_, 3, v_inst_4127_);
lean_closure_set(v___f_4141_, 4, v_toBind_4128_);
lean_closure_set(v___f_4141_, 5, v_params_4129_);
lean_closure_set(v___f_4141_, 6, v_inst_4124_);
lean_closure_set(v___f_4141_, 7, v___f_4130_);
v___x_4142_ = 0;
v___x_4143_ = lean_box(v___x_4142_);
v___f_4144_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4144_, 0, v_cinfo_4123_);
lean_closure_set(v___f_4144_, 1, v_us_4131_);
lean_closure_set(v___f_4144_, 2, v___x_4143_);
v___x_4145_ = lean_apply_2(v_inst_4127_, lean_box(0), v___f_4144_);
v___x_4146_ = lean_apply_4(v_toBind_4128_, lean_box(0), lean_box(0), v___x_4145_, v___f_4141_);
return v___x_4146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4147_, lean_object* v_toPure_4148_, lean_object* v_levels_x3f_4149_, lean_object* v_inst_4150_, lean_object* v_toBind_4151_, lean_object* v_params_4152_, lean_object* v___f_4153_, lean_object* v_cinfo_4154_){
_start:
{
lean_object* v___f_4155_; 
lean_inc(v_toBind_4151_);
lean_inc(v_inst_4150_);
lean_inc(v_levels_x3f_4149_);
lean_inc(v_toPure_4148_);
lean_inc_ref(v_cinfo_4154_);
v___f_4155_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4155_, 0, v_cinfo_4154_);
lean_closure_set(v___f_4155_, 1, v_inst_4147_);
lean_closure_set(v___f_4155_, 2, v_toPure_4148_);
lean_closure_set(v___f_4155_, 3, v_levels_x3f_4149_);
lean_closure_set(v___f_4155_, 4, v_inst_4150_);
lean_closure_set(v___f_4155_, 5, v_toBind_4151_);
lean_closure_set(v___f_4155_, 6, v_params_4152_);
lean_closure_set(v___f_4155_, 7, v___f_4153_);
if (lean_obj_tag(v_levels_x3f_4149_) == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v_toPure_4148_);
v___x_4156_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4156_, 0, v_cinfo_4154_);
v___x_4157_ = lean_apply_2(v_inst_4150_, lean_box(0), v___x_4156_);
v___x_4158_ = lean_apply_4(v_toBind_4151_, lean_box(0), lean_box(0), v___x_4157_, v___f_4155_);
return v___x_4158_;
}
else
{
lean_object* v_val_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec_ref(v_cinfo_4154_);
lean_dec(v_inst_4150_);
v_val_4159_ = lean_ctor_get(v_levels_x3f_4149_, 0);
lean_inc(v_val_4159_);
lean_dec_ref_known(v_levels_x3f_4149_, 1);
v___x_4160_ = lean_apply_2(v_toPure_4148_, lean_box(0), v_val_4159_);
v___x_4161_ = lean_apply_4(v_toBind_4151_, lean_box(0), lean_box(0), v___x_4160_, v___f_4155_);
return v___x_4161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4162_, lean_object* v_inst_4163_, lean_object* v_inst_4164_, lean_object* v_inst_4165_, lean_object* v_defaultFn_4166_, lean_object* v_levels_x3f_4167_, lean_object* v_params_4168_, lean_object* v_fieldVal_x3f_4169_){
_start:
{
lean_object* v_toApplicative_4170_; lean_object* v_toBind_4171_; lean_object* v_toPure_4172_; lean_object* v___x_4173_; lean_object* v___f_4174_; lean_object* v___f_4175_; lean_object* v___x_4176_; 
v_toApplicative_4170_ = lean_ctor_get(v_inst_4162_, 0);
v_toBind_4171_ = lean_ctor_get(v_inst_4162_, 1);
lean_inc_n(v_toBind_4171_, 2);
v_toPure_4172_ = lean_ctor_get(v_toApplicative_4170_, 1);
lean_inc_n(v_toPure_4172_, 2);
lean_inc_ref_n(v_inst_4162_, 2);
v___x_4173_ = l_Lean_getConstInfo___redArg(v_inst_4162_, v_inst_4163_, v_inst_4164_, v_defaultFn_4166_);
lean_inc(v_inst_4165_);
v___f_4174_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4174_, 0, v_inst_4162_);
lean_closure_set(v___f_4174_, 1, v_inst_4165_);
lean_closure_set(v___f_4174_, 2, v_fieldVal_x3f_4169_);
lean_closure_set(v___f_4174_, 3, v_toPure_4172_);
v___f_4175_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4175_, 0, v_inst_4162_);
lean_closure_set(v___f_4175_, 1, v_toPure_4172_);
lean_closure_set(v___f_4175_, 2, v_levels_x3f_4167_);
lean_closure_set(v___f_4175_, 3, v_inst_4165_);
lean_closure_set(v___f_4175_, 4, v_toBind_4171_);
lean_closure_set(v___f_4175_, 5, v_params_4168_);
lean_closure_set(v___f_4175_, 6, v___f_4174_);
v___x_4176_ = lean_apply_4(v_toBind_4171_, lean_box(0), lean_box(0), v___x_4173_, v___f_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4177_, lean_object* v_inst_4178_, lean_object* v_inst_4179_, lean_object* v_inst_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_defaultFn_4183_, lean_object* v_levels_x3f_4184_, lean_object* v_params_4185_, lean_object* v_fieldVal_x3f_4186_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4178_, v_inst_4179_, v_inst_4180_, v_inst_4181_, v_defaultFn_4183_, v_levels_x3f_4184_, v_params_4185_, v_fieldVal_x3f_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4188_, lean_object* v_inst_4189_, lean_object* v_inst_4190_, lean_object* v_inst_4191_, lean_object* v_inst_4192_, lean_object* v_inst_4193_, lean_object* v_defaultFn_4194_, lean_object* v_levels_x3f_4195_, lean_object* v_params_4196_, lean_object* v_fieldVal_x3f_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4188_, v_inst_4189_, v_inst_4190_, v_inst_4191_, v_inst_4192_, v_inst_4193_, v_defaultFn_4194_, v_levels_x3f_4195_, v_params_4196_, v_fieldVal_x3f_4197_);
lean_dec_ref(v_inst_4193_);
return v_res_4198_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Structure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Structure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Structure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Structure(builtin);
}
#ifdef __cplusplus
}
#endif
