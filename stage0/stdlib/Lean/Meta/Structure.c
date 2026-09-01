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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_options_12_ = lean_ctor_get(v___y_4_, 1);
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
v_ref_29_ = lean_ctor_get(v___y_26_, 4);
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
lean_object* v_toCold_388_; lean_object* v_options_389_; lean_object* v_currRecDepth_390_; lean_object* v_maxRecDepth_391_; lean_object* v_ref_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_currMacroScope_397_; uint8_t v_diag_398_; uint8_t v_suppressElabErrors_399_; lean_object* v_ref_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_toCold_388_ = lean_ctor_get(v___y_385_, 0);
v_options_389_ = lean_ctor_get(v___y_385_, 1);
v_currRecDepth_390_ = lean_ctor_get(v___y_385_, 2);
v_maxRecDepth_391_ = lean_ctor_get(v___y_385_, 3);
v_ref_392_ = lean_ctor_get(v___y_385_, 4);
v_currNamespace_393_ = lean_ctor_get(v___y_385_, 5);
v_openDecls_394_ = lean_ctor_get(v___y_385_, 6);
v_initHeartbeats_395_ = lean_ctor_get(v___y_385_, 7);
v_maxHeartbeats_396_ = lean_ctor_get(v___y_385_, 8);
v_currMacroScope_397_ = lean_ctor_get(v___y_385_, 9);
v_diag_398_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*10);
v_suppressElabErrors_399_ = lean_ctor_get_uint8(v___y_385_, sizeof(void*)*10 + 1);
v_ref_400_ = l_Lean_replaceRef(v_ref_381_, v_ref_392_);
lean_inc(v_currMacroScope_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc(v_maxRecDepth_391_);
lean_inc(v_currRecDepth_390_);
lean_inc_ref(v_options_389_);
lean_inc_ref(v_toCold_388_);
v___x_401_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_401_, 0, v_toCold_388_);
lean_ctor_set(v___x_401_, 1, v_options_389_);
lean_ctor_set(v___x_401_, 2, v_currRecDepth_390_);
lean_ctor_set(v___x_401_, 3, v_maxRecDepth_391_);
lean_ctor_set(v___x_401_, 4, v_ref_400_);
lean_ctor_set(v___x_401_, 5, v_currNamespace_393_);
lean_ctor_set(v___x_401_, 6, v_openDecls_394_);
lean_ctor_set(v___x_401_, 7, v_initHeartbeats_395_);
lean_ctor_set(v___x_401_, 8, v_maxHeartbeats_396_);
lean_ctor_set(v___x_401_, 9, v_currMacroScope_397_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*10, v_diag_398_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*10 + 1, v_suppressElabErrors_399_);
v___x_402_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_382_, v___y_383_, v___y_384_, v___x_401_, v___y_386_);
lean_dec_ref_known(v___x_401_, 10);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_403_, lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_403_, v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v_ref_403_);
return v_res_410_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_420_, lean_object* v_projName_421_, lean_object* v_n_422_, lean_object* v_ref_423_, lean_object* v___f_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
if (v___x_420_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_430_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_431_ = l_Lean_MessageData_ofName(v_projName_421_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_MessageData_ofConstName(v_n_422_, v___x_420_);
v___x_436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_423_, v___x_438_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
v___x_441_ = lean_apply_6(v___f_424_, v_a_440_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, lean_box(0));
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v___f_424_);
v_a_442_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_439_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v_n_422_);
lean_dec(v_projName_421_);
v___x_450_ = lean_box(0);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc(v___y_426_);
lean_inc_ref(v___y_425_);
v___x_451_ = lean_apply_6(v___f_424_, v___x_450_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, lean_box(0));
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_452_, lean_object* v_projName_453_, lean_object* v_n_454_, lean_object* v_ref_455_, lean_object* v___f_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_17238__boxed_462_; lean_object* v_res_463_; 
v___x_17238__boxed_462_ = lean_unbox(v___x_452_);
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17238__boxed_462_, v_projName_453_, v_n_454_, v_ref_455_, v___f_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v_ref_455_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_464_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_470_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
lean_ctor_set(v___x_470_, 3, v___x_469_);
lean_ctor_set(v___x_470_, 4, v___x_469_);
lean_ctor_set(v___x_470_, 5, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_471_, uint8_t v_s_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; lean_object* v_env_477_; lean_object* v_nextMacroScope_478_; lean_object* v_ngen_479_; lean_object* v_auxDeclNGen_480_; lean_object* v_traceState_481_; lean_object* v_messages_482_; lean_object* v_infoState_483_; lean_object* v_snapshotTasks_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_513_; 
v___x_476_ = lean_st_ref_take(v___y_474_);
v_env_477_ = lean_ctor_get(v___x_476_, 0);
v_nextMacroScope_478_ = lean_ctor_get(v___x_476_, 1);
v_ngen_479_ = lean_ctor_get(v___x_476_, 2);
v_auxDeclNGen_480_ = lean_ctor_get(v___x_476_, 3);
v_traceState_481_ = lean_ctor_get(v___x_476_, 4);
v_messages_482_ = lean_ctor_get(v___x_476_, 6);
v_infoState_483_ = lean_ctor_get(v___x_476_, 7);
v_snapshotTasks_484_ = lean_ctor_get(v___x_476_, 8);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___x_476_, 5);
lean_dec(v_unused_514_);
v___x_486_ = v___x_476_;
v_isShared_487_ = v_isSharedCheck_513_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snapshotTasks_484_);
lean_inc(v_infoState_483_);
lean_inc(v_messages_482_);
lean_inc(v_traceState_481_);
lean_inc(v_auxDeclNGen_480_);
lean_inc(v_ngen_479_);
lean_inc(v_nextMacroScope_478_);
lean_inc(v_env_477_);
lean_dec(v___x_476_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_513_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_488_ = 0;
v___x_489_ = lean_box(0);
v___x_490_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_477_, v_declName_471_, v_s_472_, v___x_488_, v___x_489_);
v___x_491_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 5, v___x_491_);
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_493_ = v___x_486_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_nextMacroScope_478_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_ngen_479_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_auxDeclNGen_480_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_traceState_481_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v_messages_482_);
lean_ctor_set(v_reuseFailAlloc_512_, 7, v_infoState_483_);
lean_ctor_set(v_reuseFailAlloc_512_, 8, v_snapshotTasks_484_);
v___x_493_ = v_reuseFailAlloc_512_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_mctx_496_; lean_object* v_zetaDeltaFVarIds_497_; lean_object* v_postponed_498_; lean_object* v_diag_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_510_; 
v___x_494_ = lean_st_ref_put(v___y_474_, v___x_493_);
v___x_495_ = lean_st_ref_take(v___y_473_);
v_mctx_496_ = lean_ctor_get(v___x_495_, 0);
v_zetaDeltaFVarIds_497_ = lean_ctor_get(v___x_495_, 2);
v_postponed_498_ = lean_ctor_get(v___x_495_, 3);
v_diag_499_ = lean_ctor_get(v___x_495_, 4);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v___x_495_, 1);
lean_dec(v_unused_511_);
v___x_501_ = v___x_495_;
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_diag_499_);
lean_inc(v_postponed_498_);
lean_inc(v_zetaDeltaFVarIds_497_);
lean_inc(v_mctx_496_);
lean_dec(v___x_495_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_510_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 1, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_mctx_496_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_zetaDeltaFVarIds_497_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_postponed_498_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_diag_499_);
v___x_505_ = v_reuseFailAlloc_509_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_st_ref_put(v___y_473_, v___x_505_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_515_, lean_object* v_s_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v_s_boxed_520_; lean_object* v_res_521_; 
v_s_boxed_520_ = lean_unbox(v_s_516_);
v_res_521_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_515_, v_s_boxed_520_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec(v___y_517_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_528_; lean_object* v___x_529_; 
v___x_528_ = 0;
v___x_529_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_522_, v___x_528_, v___y_524_, v___y_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_546_, lean_object* v_projName_547_, lean_object* v___x_548_, lean_object* v_a_549_, uint8_t v_instImplicit_550_, lean_object* v___x_551_, lean_object* v_params_552_, lean_object* v_self_553_, lean_object* v_b_554_, uint8_t v___x_555_, lean_object* v_a_556_, lean_object* v___x_557_, lean_object* v_paramInfoOverrides_558_, lean_object* v_n_559_, lean_object* v_ref_560_, lean_object* v___x_561_, uint8_t v_a_562_, lean_object* v_____r_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = l_List_lengthTR___redArg(v_paramInfoOverrides_558_);
v___x_729_ = lean_array_get_size(v_params_552_);
v___x_730_ = lean_nat_dec_le(v___x_728_, v___x_729_);
lean_dec(v___x_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_547_);
v___x_732_ = l_Lean_MessageData_ofName(v_projName_547_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v_n_559_);
v___x_736_ = l_Lean_MessageData_ofConstName(v_n_559_, v___x_730_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_560_, v___x_739_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref_known(v___x_740_, 1);
goto v___jp_689_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_561_);
lean_dec(v_n_559_);
lean_dec_ref(v_a_556_);
lean_dec_ref(v_self_553_);
lean_dec(v___x_551_);
lean_dec(v_a_549_);
lean_dec(v___x_548_);
lean_dec(v_projName_547_);
lean_dec_ref(v___x_546_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
goto v___jp_689_;
}
v___jp_569_:
{
lean_object* v___x_572_; lean_object* v_env_573_; lean_object* v_nextMacroScope_574_; lean_object* v_ngen_575_; lean_object* v_auxDeclNGen_576_; lean_object* v_traceState_577_; lean_object* v_messages_578_; lean_object* v_infoState_579_; lean_object* v_snapshotTasks_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_612_; 
v___x_572_ = lean_st_ref_take(v___y_570_);
v_env_573_ = lean_ctor_get(v___x_572_, 0);
v_nextMacroScope_574_ = lean_ctor_get(v___x_572_, 1);
v_ngen_575_ = lean_ctor_get(v___x_572_, 2);
v_auxDeclNGen_576_ = lean_ctor_get(v___x_572_, 3);
v_traceState_577_ = lean_ctor_get(v___x_572_, 4);
v_messages_578_ = lean_ctor_get(v___x_572_, 6);
v_infoState_579_ = lean_ctor_get(v___x_572_, 7);
v_snapshotTasks_580_ = lean_ctor_get(v___x_572_, 8);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_572_, 5);
lean_dec(v_unused_613_);
v___x_582_ = v___x_572_;
v_isShared_583_ = v_isSharedCheck_612_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snapshotTasks_580_);
lean_inc(v_infoState_579_);
lean_inc(v_messages_578_);
lean_inc(v_traceState_577_);
lean_inc(v_auxDeclNGen_576_);
lean_inc(v_ngen_575_);
lean_inc(v_nextMacroScope_574_);
lean_inc(v_env_573_);
lean_dec(v___x_572_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_612_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_name_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_name_584_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_name_584_);
lean_dec_ref(v___x_546_);
lean_inc(v_projName_547_);
v___x_585_ = l_Lean_addProjectionFnInfo(v_env_573_, v_projName_547_, v_name_584_, v___x_548_, v_a_549_, v_instImplicit_550_);
v___x_586_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 5, v___x_586_);
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_588_ = v___x_582_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_nextMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_ngen_575_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_auxDeclNGen_576_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_traceState_577_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_messages_578_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_infoState_579_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v_snapshotTasks_580_);
v___x_588_ = v_reuseFailAlloc_611_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_mctx_591_; lean_object* v_zetaDeltaFVarIds_592_; lean_object* v_postponed_593_; lean_object* v_diag_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_609_; 
v___x_589_ = lean_st_ref_put(v___y_570_, v___x_588_);
v___x_590_ = lean_st_ref_take(v___y_571_);
v_mctx_591_ = lean_ctor_get(v___x_590_, 0);
v_zetaDeltaFVarIds_592_ = lean_ctor_get(v___x_590_, 2);
v_postponed_593_ = lean_ctor_get(v___x_590_, 3);
v_diag_594_ = lean_ctor_get(v___x_590_, 4);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_590_, 1);
lean_dec(v_unused_610_);
v___x_596_ = v___x_590_;
v_isShared_597_ = v_isSharedCheck_609_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_diag_594_);
lean_inc(v_postponed_593_);
lean_inc(v_zetaDeltaFVarIds_592_);
lean_inc(v_mctx_591_);
lean_dec(v___x_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_609_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_mctx_591_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_zetaDeltaFVarIds_592_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_postponed_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_diag_594_);
v___x_600_ = v_reuseFailAlloc_608_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_601_ = lean_st_ref_put(v___y_571_, v___x_600_);
v___x_602_ = l_Lean_Expr_const___override(v_projName_547_, v___x_551_);
v___x_603_ = l_Lean_mkAppN(v___x_602_, v_params_552_);
v___x_604_ = l_Lean_Expr_app___override(v___x_603_, v_self_553_);
v___x_605_ = l_Lean_Expr_bindingBody_x21(v_b_554_);
v___x_606_ = lean_expr_instantiate1(v___x_605_, v___x_604_);
lean_dec_ref(v___x_604_);
lean_dec_ref(v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
}
}
}
v___jp_614_:
{
if (lean_obj_tag(v___y_617_) == 0)
{
lean_dec_ref_known(v___y_617_, 1);
v___y_570_ = v___y_615_;
v___y_571_ = v___y_616_;
goto v___jp_569_;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_self_553_);
lean_dec(v___x_551_);
lean_dec(v_a_549_);
lean_dec(v___x_548_);
lean_dec(v_projName_547_);
lean_dec_ref(v___x_546_);
v_a_618_ = lean_ctor_get(v___y_617_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___y_617_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___y_617_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___y_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_633_ = lean_box(0);
lean_inc(v_projName_547_);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v_projName_547_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_635_, 0, v___y_630_);
lean_ctor_set(v___x_635_, 1, v___y_631_);
lean_ctor_set(v___x_635_, 2, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3, v___x_555_);
v___x_636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = l_Lean_addDecl(v___x_636_, v___y_629_, v___y_632_, v___y_627_);
lean_dec_ref(v___y_632_);
v___y_615_ = v___y_627_;
v___y_616_ = v___y_628_;
v___y_617_ = v___x_637_;
goto v___jp_614_;
}
v___jp_638_:
{
uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v_toCold_647_; lean_object* v_options_648_; lean_object* v_currRecDepth_649_; lean_object* v_maxRecDepth_650_; lean_object* v_ref_651_; lean_object* v_currNamespace_652_; lean_object* v_openDecls_653_; lean_object* v_initHeartbeats_654_; lean_object* v_maxHeartbeats_655_; lean_object* v_currMacroScope_656_; uint8_t v_diag_657_; uint8_t v_suppressElabErrors_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_ref_663_; lean_object* v___x_664_; 
v___x_645_ = 0;
lean_inc_ref(v_a_556_);
v___x_646_ = l_Lean_LocalContext_mkForall(v_a_556_, v___x_557_, v___y_640_, v___x_555_, v___x_645_);
lean_dec_ref(v___y_640_);
v_toCold_647_ = lean_ctor_get(v___y_643_, 0);
v_options_648_ = lean_ctor_get(v___y_643_, 1);
v_currRecDepth_649_ = lean_ctor_get(v___y_643_, 2);
v_maxRecDepth_650_ = lean_ctor_get(v___y_643_, 3);
v_ref_651_ = lean_ctor_get(v___y_643_, 4);
v_currNamespace_652_ = lean_ctor_get(v___y_643_, 5);
v_openDecls_653_ = lean_ctor_get(v___y_643_, 6);
v_initHeartbeats_654_ = lean_ctor_get(v___y_643_, 7);
v_maxHeartbeats_655_ = lean_ctor_get(v___y_643_, 8);
v_currMacroScope_656_ = lean_ctor_get(v___y_643_, 9);
v_diag_657_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*10);
v_suppressElabErrors_658_ = lean_ctor_get_uint8(v___y_643_, sizeof(void*)*10 + 1);
v___x_659_ = l_Lean_Expr_inferImplicit(v___x_646_, v___x_548_, v___x_555_);
v___x_660_ = l_Lean_Expr_updateForallBinderInfos(v___x_659_, v_paramInfoOverrides_558_);
lean_inc_ref(v_self_553_);
lean_inc(v_a_549_);
v___x_661_ = l_Lean_Expr_proj___override(v_n_559_, v_a_549_, v_self_553_);
v___x_662_ = l_Lean_LocalContext_mkLambda(v_a_556_, v___x_557_, v___x_661_, v___x_555_, v___x_645_);
lean_dec_ref(v___x_661_);
v_ref_663_ = l_Lean_replaceRef(v_ref_560_, v_ref_651_);
lean_inc(v_currMacroScope_656_);
lean_inc(v_maxHeartbeats_655_);
lean_inc(v_initHeartbeats_654_);
lean_inc(v_openDecls_653_);
lean_inc(v_currNamespace_652_);
lean_inc(v_maxRecDepth_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_options_648_);
lean_inc_ref(v_toCold_647_);
v___x_664_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_664_, 0, v_toCold_647_);
lean_ctor_set(v___x_664_, 1, v_options_648_);
lean_ctor_set(v___x_664_, 2, v_currRecDepth_649_);
lean_ctor_set(v___x_664_, 3, v_maxRecDepth_650_);
lean_ctor_set(v___x_664_, 4, v_ref_663_);
lean_ctor_set(v___x_664_, 5, v_currNamespace_652_);
lean_ctor_set(v___x_664_, 6, v_openDecls_653_);
lean_ctor_set(v___x_664_, 7, v_initHeartbeats_654_);
lean_ctor_set(v___x_664_, 8, v_maxHeartbeats_655_);
lean_ctor_set(v___x_664_, 9, v_currMacroScope_656_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*10, v_diag_657_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*10 + 1, v_suppressElabErrors_658_);
if (v___y_639_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(1);
lean_inc(v_projName_547_);
v___x_666_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_547_, v___x_561_, v___x_660_, v___x_662_, v___x_665_, v___y_644_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v_a_667_);
v___x_669_ = l_Lean_addDecl(v___x_668_, v___x_645_, v___x_664_, v___y_644_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_dec_ref_known(v___x_669_, 1);
if (v_instImplicit_550_ == 0)
{
lean_object* v___x_670_; 
lean_inc(v_projName_547_);
v___x_670_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_547_, v___y_641_, v___y_642_, v___x_664_, v___y_644_);
lean_dec_ref_known(v___x_664_, 10);
v___y_615_ = v___y_644_;
v___y_616_ = v___y_642_;
v___y_617_ = v___x_670_;
goto v___jp_614_;
}
else
{
lean_dec_ref_known(v___x_664_, 10);
v___y_570_ = v___y_644_;
v___y_571_ = v___y_642_;
goto v___jp_569_;
}
}
else
{
lean_dec_ref_known(v___x_664_, 10);
v___y_615_ = v___y_644_;
v___y_616_ = v___y_642_;
v___y_617_ = v___x_669_;
goto v___jp_614_;
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref_known(v___x_664_, 10);
lean_dec_ref(v_self_553_);
lean_dec(v___x_551_);
lean_dec(v_a_549_);
lean_dec(v___x_548_);
lean_dec(v_projName_547_);
lean_dec_ref(v___x_546_);
v_a_671_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_666_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_666_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v___x_679_; lean_object* v_env_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_st_ref_get(v___y_644_);
v_env_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref_n(v_env_680_, 2);
lean_dec(v___x_679_);
lean_inc_ref(v___x_660_);
lean_inc(v_projName_547_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_projName_547_);
lean_ctor_set(v___x_681_, 1, v___x_561_);
lean_ctor_set(v___x_681_, 2, v___x_660_);
v___x_682_ = l_Lean_Environment_hasUnsafe(v_env_680_, v___x_660_);
lean_dec_ref(v___x_660_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Environment_hasUnsafe(v_env_680_, v___x_662_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_684_ = lean_box(0);
lean_inc(v_projName_547_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v_projName_547_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_681_);
lean_ctor_set(v___x_686_, 1, v___x_662_);
lean_ctor_set(v___x_686_, 2, v___x_685_);
v___x_687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = l_Lean_addDecl(v___x_687_, v___x_645_, v___x_664_, v___y_644_);
lean_dec_ref_known(v___x_664_, 10);
v___y_615_ = v___y_644_;
v___y_616_ = v___y_642_;
v___y_617_ = v___x_688_;
goto v___jp_614_;
}
else
{
v___y_627_ = v___y_644_;
v___y_628_ = v___y_642_;
v___y_629_ = v___x_645_;
v___y_630_ = v___x_681_;
v___y_631_ = v___x_662_;
v___y_632_ = v___x_664_;
goto v___jp_626_;
}
}
else
{
lean_dec_ref(v_env_680_);
v___y_627_ = v___y_644_;
v___y_628_ = v___y_642_;
v___y_629_ = v___x_645_;
v___y_630_ = v___x_681_;
v___y_631_ = v___x_662_;
v___y_632_ = v___x_664_;
goto v___jp_626_;
}
}
}
v___jp_689_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_Expr_bindingDomain_x21(v_b_554_);
v___x_691_ = lean_expr_consume_type_annotations(v___x_690_);
lean_inc_ref(v___x_691_);
v___x_692_ = l_Lean_Meta_isProp(v___x_691_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_692_) == 0)
{
if (v_a_562_ == 0)
{
lean_object* v_a_693_; uint8_t v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_unbox(v_a_693_);
lean_dec(v_a_693_);
v___y_639_ = v___x_694_;
v___y_640_ = v___x_691_;
v___y_641_ = v___y_564_;
v___y_642_ = v___y_565_;
v___y_643_ = v___y_566_;
v___y_644_ = v___y_567_;
goto v___jp_638_;
}
else
{
lean_object* v_a_695_; uint8_t v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_692_, 1);
v___x_696_ = lean_unbox(v_a_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_697_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_547_);
v___x_698_ = l_Lean_MessageData_ofName(v_projName_547_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_unbox(v_a_695_);
lean_inc(v_n_559_);
v___x_703_ = l_Lean_MessageData_ofConstName(v_n_559_, v___x_702_);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_701_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_inc_ref(v___x_691_);
v___x_707_ = l_Lean_indentExpr(v___x_691_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_560_, v___x_708_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_709_) == 0)
{
uint8_t v___x_710_; 
lean_dec_ref_known(v___x_709_, 1);
v___x_710_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
v___y_639_ = v___x_710_;
v___y_640_ = v___x_691_;
v___y_641_ = v___y_564_;
v___y_642_ = v___y_565_;
v___y_643_ = v___y_566_;
v___y_644_ = v___y_567_;
goto v___jp_638_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_695_);
lean_dec_ref(v___x_691_);
lean_dec(v___x_561_);
lean_dec(v_n_559_);
lean_dec_ref(v_a_556_);
lean_dec_ref(v_self_553_);
lean_dec(v___x_551_);
lean_dec(v_a_549_);
lean_dec(v___x_548_);
lean_dec(v_projName_547_);
lean_dec_ref(v___x_546_);
v_a_711_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_709_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
v___y_639_ = v___x_719_;
v___y_640_ = v___x_691_;
v___y_641_ = v___y_564_;
v___y_642_ = v___y_565_;
v___y_643_ = v___y_566_;
v___y_644_ = v___y_567_;
goto v___jp_638_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___x_691_);
lean_dec(v___x_561_);
lean_dec(v_n_559_);
lean_dec_ref(v_a_556_);
lean_dec_ref(v_self_553_);
lean_dec(v___x_551_);
lean_dec(v_a_549_);
lean_dec(v___x_548_);
lean_dec(v_projName_547_);
lean_dec_ref(v___x_546_);
v_a_720_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_692_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_692_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_749_ = _args[0];
lean_object* v_projName_750_ = _args[1];
lean_object* v___x_751_ = _args[2];
lean_object* v_a_752_ = _args[3];
lean_object* v_instImplicit_753_ = _args[4];
lean_object* v___x_754_ = _args[5];
lean_object* v_params_755_ = _args[6];
lean_object* v_self_756_ = _args[7];
lean_object* v_b_757_ = _args[8];
lean_object* v___x_758_ = _args[9];
lean_object* v_a_759_ = _args[10];
lean_object* v___x_760_ = _args[11];
lean_object* v_paramInfoOverrides_761_ = _args[12];
lean_object* v_n_762_ = _args[13];
lean_object* v_ref_763_ = _args[14];
lean_object* v___x_764_ = _args[15];
lean_object* v_a_765_ = _args[16];
lean_object* v_____r_766_ = _args[17];
lean_object* v___y_767_ = _args[18];
lean_object* v___y_768_ = _args[19];
lean_object* v___y_769_ = _args[20];
lean_object* v___y_770_ = _args[21];
lean_object* v___y_771_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_772_; uint8_t v___x_17477__boxed_773_; uint8_t v_a_17483__boxed_774_; lean_object* v_res_775_; 
v_instImplicit_boxed_772_ = lean_unbox(v_instImplicit_753_);
v___x_17477__boxed_773_ = lean_unbox(v___x_758_);
v_a_17483__boxed_774_ = lean_unbox(v_a_765_);
v_res_775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_749_, v_projName_750_, v___x_751_, v_a_752_, v_instImplicit_boxed_772_, v___x_754_, v_params_755_, v_self_756_, v_b_757_, v___x_17477__boxed_773_, v_a_759_, v___x_760_, v_paramInfoOverrides_761_, v_n_762_, v_ref_763_, v___x_764_, v_a_17483__boxed_774_, v_____r_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v_ref_763_);
lean_dec(v_paramInfoOverrides_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v_b_757_);
lean_dec_ref(v_params_755_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_776_, uint8_t v_isExporting_777_, lean_object* v___x_778_, lean_object* v___y_779_, lean_object* v___x_780_, lean_object* v_a_x3f_781_){
_start:
{
lean_object* v___x_783_; lean_object* v_env_784_; lean_object* v_nextMacroScope_785_; lean_object* v_ngen_786_; lean_object* v_auxDeclNGen_787_; lean_object* v_traceState_788_; lean_object* v_messages_789_; lean_object* v_infoState_790_; lean_object* v_snapshotTasks_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_816_; 
v___x_783_ = lean_st_ref_take(v___y_776_);
v_env_784_ = lean_ctor_get(v___x_783_, 0);
v_nextMacroScope_785_ = lean_ctor_get(v___x_783_, 1);
v_ngen_786_ = lean_ctor_get(v___x_783_, 2);
v_auxDeclNGen_787_ = lean_ctor_get(v___x_783_, 3);
v_traceState_788_ = lean_ctor_get(v___x_783_, 4);
v_messages_789_ = lean_ctor_get(v___x_783_, 6);
v_infoState_790_ = lean_ctor_get(v___x_783_, 7);
v_snapshotTasks_791_ = lean_ctor_get(v___x_783_, 8);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_783_, 5);
lean_dec(v_unused_817_);
v___x_793_ = v___x_783_;
v_isShared_794_ = v_isSharedCheck_816_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snapshotTasks_791_);
lean_inc(v_infoState_790_);
lean_inc(v_messages_789_);
lean_inc(v_traceState_788_);
lean_inc(v_auxDeclNGen_787_);
lean_inc(v_ngen_786_);
lean_inc(v_nextMacroScope_785_);
lean_inc(v_env_784_);
lean_dec(v___x_783_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_816_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_Environment_setExporting(v_env_784_, v_isExporting_777_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 5, v___x_778_);
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_nextMacroScope_785_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_ngen_786_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_auxDeclNGen_787_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_traceState_788_);
lean_ctor_set(v_reuseFailAlloc_815_, 5, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_815_, 6, v_messages_789_);
lean_ctor_set(v_reuseFailAlloc_815_, 7, v_infoState_790_);
lean_ctor_set(v_reuseFailAlloc_815_, 8, v_snapshotTasks_791_);
v___x_797_ = v_reuseFailAlloc_815_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_mctx_800_; lean_object* v_zetaDeltaFVarIds_801_; lean_object* v_postponed_802_; lean_object* v_diag_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v___x_798_ = lean_st_ref_put(v___y_776_, v___x_797_);
v___x_799_ = lean_st_ref_take(v___y_779_);
v_mctx_800_ = lean_ctor_get(v___x_799_, 0);
v_zetaDeltaFVarIds_801_ = lean_ctor_get(v___x_799_, 2);
v_postponed_802_ = lean_ctor_get(v___x_799_, 3);
v_diag_803_ = lean_ctor_get(v___x_799_, 4);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v___x_799_, 1);
lean_dec(v_unused_814_);
v___x_805_ = v___x_799_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_diag_803_);
lean_inc(v_postponed_802_);
lean_inc(v_zetaDeltaFVarIds_801_);
lean_inc(v_mctx_800_);
lean_dec(v___x_799_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_780_);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_mctx_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_zetaDeltaFVarIds_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_postponed_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_diag_803_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_st_ref_put(v___y_779_, v___x_808_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_818_, lean_object* v_isExporting_819_, lean_object* v___x_820_, lean_object* v___y_821_, lean_object* v___x_822_, lean_object* v_a_x3f_823_, lean_object* v___y_824_){
_start:
{
uint8_t v_isExporting_boxed_825_; lean_object* v_res_826_; 
v_isExporting_boxed_825_ = lean_unbox(v_isExporting_819_);
v_res_826_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_818_, v_isExporting_boxed_825_, v___x_820_, v___y_821_, v___x_822_, v_a_x3f_823_);
lean_dec(v_a_x3f_823_);
lean_dec(v___y_821_);
lean_dec(v___y_818_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_827_, uint8_t v_isExporting_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v_env_835_; lean_object* v___x_836_; uint8_t v_isModule_837_; 
v___x_834_ = lean_st_ref_get(v___y_832_);
v_env_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc_ref(v_env_835_);
lean_dec(v___x_834_);
v___x_836_ = l_Lean_Environment_header(v_env_835_);
v_isModule_837_ = lean_ctor_get_uint8(v___x_836_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_836_);
if (v_isModule_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_env_835_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_838_ = lean_apply_5(v_x_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
return v___x_838_;
}
else
{
uint8_t v_isExporting_839_; 
v_isExporting_839_ = lean_ctor_get_uint8(v_env_835_, sizeof(void*)*8);
lean_dec_ref(v_env_835_);
if (v_isExporting_828_ == 0)
{
if (v_isExporting_839_ == 0)
{
lean_object* v___x_905_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_905_ = lean_apply_5(v_x_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
return v___x_905_;
}
else
{
goto v___jp_840_;
}
}
else
{
if (v_isExporting_839_ == 0)
{
goto v___jp_840_;
}
else
{
lean_object* v___x_906_; 
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_906_ = lean_apply_5(v_x_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
return v___x_906_;
}
}
v___jp_840_:
{
lean_object* v___x_841_; lean_object* v_env_842_; lean_object* v_nextMacroScope_843_; lean_object* v_ngen_844_; lean_object* v_auxDeclNGen_845_; lean_object* v_traceState_846_; lean_object* v_messages_847_; lean_object* v_infoState_848_; lean_object* v_snapshotTasks_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_903_; 
v___x_841_ = lean_st_ref_take(v___y_832_);
v_env_842_ = lean_ctor_get(v___x_841_, 0);
v_nextMacroScope_843_ = lean_ctor_get(v___x_841_, 1);
v_ngen_844_ = lean_ctor_get(v___x_841_, 2);
v_auxDeclNGen_845_ = lean_ctor_get(v___x_841_, 3);
v_traceState_846_ = lean_ctor_get(v___x_841_, 4);
v_messages_847_ = lean_ctor_get(v___x_841_, 6);
v_infoState_848_ = lean_ctor_get(v___x_841_, 7);
v_snapshotTasks_849_ = lean_ctor_get(v___x_841_, 8);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v___x_841_, 5);
lean_dec(v_unused_904_);
v___x_851_ = v___x_841_;
v_isShared_852_ = v_isSharedCheck_903_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snapshotTasks_849_);
lean_inc(v_infoState_848_);
lean_inc(v_messages_847_);
lean_inc(v_traceState_846_);
lean_inc(v_auxDeclNGen_845_);
lean_inc(v_ngen_844_);
lean_inc(v_nextMacroScope_843_);
lean_inc(v_env_842_);
lean_dec(v___x_841_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_903_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = l_Lean_Environment_setExporting(v_env_842_, v_isExporting_828_);
v___x_854_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 5, v___x_854_);
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_nextMacroScope_843_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_ngen_844_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_auxDeclNGen_845_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_traceState_846_);
lean_ctor_set(v_reuseFailAlloc_902_, 5, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_902_, 6, v_messages_847_);
lean_ctor_set(v_reuseFailAlloc_902_, 7, v_infoState_848_);
lean_ctor_set(v_reuseFailAlloc_902_, 8, v_snapshotTasks_849_);
v___x_856_ = v_reuseFailAlloc_902_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_mctx_859_; lean_object* v_zetaDeltaFVarIds_860_; lean_object* v_postponed_861_; lean_object* v_diag_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_900_; 
v___x_857_ = lean_st_ref_put(v___y_832_, v___x_856_);
v___x_858_ = lean_st_ref_take(v___y_830_);
v_mctx_859_ = lean_ctor_get(v___x_858_, 0);
v_zetaDeltaFVarIds_860_ = lean_ctor_get(v___x_858_, 2);
v_postponed_861_ = lean_ctor_get(v___x_858_, 3);
v_diag_862_ = lean_ctor_get(v___x_858_, 4);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_858_, 1);
lean_dec(v_unused_901_);
v___x_864_ = v___x_858_;
v_isShared_865_ = v_isSharedCheck_900_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_diag_862_);
lean_inc(v_postponed_861_);
lean_inc(v_zetaDeltaFVarIds_860_);
lean_inc(v_mctx_859_);
lean_dec(v___x_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_900_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_866_);
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_mctx_859_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_zetaDeltaFVarIds_860_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_postponed_861_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_diag_862_);
v___x_868_ = v_reuseFailAlloc_899_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v_r_870_; 
v___x_869_ = lean_st_ref_put(v___y_830_, v___x_868_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v_r_870_ = lean_apply_5(v_x_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
if (lean_obj_tag(v_r_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_887_; 
v_a_871_ = lean_ctor_get(v_r_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_r_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_873_ = v_r_870_;
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v_r_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
lean_inc(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 1);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_886_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v___x_877_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_832_, v_isExporting_839_, v___x_854_, v___y_830_, v___x_866_, v___x_876_);
lean_dec_ref(v___x_876_);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_885_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_a_871_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_871_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_888_ = lean_ctor_get(v_r_870_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v_r_870_, 1);
v___x_889_ = lean_box(0);
v___x_890_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_832_, v_isExporting_839_, v___x_854_, v___y_830_, v___x_866_, v___x_889_);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_890_, 0);
lean_dec(v_unused_898_);
v___x_892_ = v___x_890_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
lean_ctor_set(v___x_892_, 0, v_a_888_);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_888_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_907_, lean_object* v_isExporting_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
uint8_t v_isExporting_boxed_914_; lean_object* v_res_915_; 
v_isExporting_boxed_914_ = lean_unbox(v_isExporting_908_);
v_res_915_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_907_, v_isExporting_boxed_914_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_916_, uint8_t v_when_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
if (v_when_917_ == 0)
{
lean_object* v___x_923_; 
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_923_ = lean_apply_5(v_x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_923_;
}
else
{
uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_924_ = 0;
v___x_925_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_916_, v___x_924_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_926_, lean_object* v_when_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v_when_boxed_933_; lean_object* v_res_934_; 
v_when_boxed_933_ = lean_unbox(v_when_927_);
v_res_934_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_926_, v_when_boxed_933_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_935_, lean_object* v_projDecls_936_, lean_object* v___x_937_, lean_object* v___x_938_, uint8_t v_instImplicit_939_, lean_object* v___x_940_, lean_object* v_params_941_, lean_object* v_self_942_, lean_object* v_a_943_, lean_object* v___x_944_, lean_object* v_n_945_, lean_object* v___x_946_, uint8_t v_a_947_, lean_object* v_a_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_lt(v_a_948_, v_upperBound_935_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_a_948_);
lean_dec(v___x_946_);
lean_dec(v_n_945_);
lean_dec_ref(v___x_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_self_942_);
lean_dec_ref(v_params_941_);
lean_dec(v___x_940_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_949_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_ref_958_; lean_object* v_projName_959_; lean_object* v_paramInfoOverrides_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___f_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___y_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
v___x_957_ = lean_array_fget_borrowed(v_projDecls_936_, v_a_948_);
v_ref_958_ = lean_ctor_get(v___x_957_, 0);
v_projName_959_ = lean_ctor_get(v___x_957_, 1);
v_paramInfoOverrides_960_ = lean_ctor_get(v___x_957_, 2);
v___x_961_ = lean_box(v_instImplicit_939_);
v___x_962_ = lean_box(v___x_955_);
v___x_963_ = lean_box(v_a_947_);
lean_inc(v___x_946_);
lean_inc_n(v_ref_958_, 2);
lean_inc_n(v_n_945_, 2);
lean_inc(v_paramInfoOverrides_960_);
lean_inc_ref(v___x_944_);
lean_inc_ref(v_a_943_);
lean_inc_ref(v_b_949_);
lean_inc_ref(v_self_942_);
lean_inc_ref(v_params_941_);
lean_inc(v___x_940_);
lean_inc(v_a_948_);
lean_inc(v___x_938_);
lean_inc_n(v_projName_959_, 2);
lean_inc_ref(v___x_937_);
v___f_964_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_964_, 0, v___x_937_);
lean_closure_set(v___f_964_, 1, v_projName_959_);
lean_closure_set(v___f_964_, 2, v___x_938_);
lean_closure_set(v___f_964_, 3, v_a_948_);
lean_closure_set(v___f_964_, 4, v___x_961_);
lean_closure_set(v___f_964_, 5, v___x_940_);
lean_closure_set(v___f_964_, 6, v_params_941_);
lean_closure_set(v___f_964_, 7, v_self_942_);
lean_closure_set(v___f_964_, 8, v_b_949_);
lean_closure_set(v___f_964_, 9, v___x_962_);
lean_closure_set(v___f_964_, 10, v_a_943_);
lean_closure_set(v___f_964_, 11, v___x_944_);
lean_closure_set(v___f_964_, 12, v_paramInfoOverrides_960_);
lean_closure_set(v___f_964_, 13, v_n_945_);
lean_closure_set(v___f_964_, 14, v_ref_958_);
lean_closure_set(v___f_964_, 15, v___x_946_);
lean_closure_set(v___f_964_, 16, v___x_963_);
v___x_965_ = l_Lean_Expr_isForall(v_b_949_);
lean_dec_ref(v_b_949_);
v___x_966_ = lean_box(v___x_965_);
v___y_967_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_967_, 0, v___x_966_);
lean_closure_set(v___y_967_, 1, v_projName_959_);
lean_closure_set(v___y_967_, 2, v_n_945_);
lean_closure_set(v___y_967_, 3, v_ref_958_);
lean_closure_set(v___y_967_, 4, v___f_964_);
v___x_968_ = l_Lean_isPrivateName(v_projName_959_);
v___x_969_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_967_, v___x_968_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_a_948_, v___x_971_);
lean_dec(v_a_948_);
v_a_948_ = v___x_972_;
v_b_949_ = v_a_970_;
goto _start;
}
else
{
lean_dec(v_a_948_);
lean_dec(v___x_946_);
lean_dec(v_n_945_);
lean_dec_ref(v___x_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_self_942_);
lean_dec_ref(v_params_941_);
lean_dec(v___x_940_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_974_ = _args[0];
lean_object* v_projDecls_975_ = _args[1];
lean_object* v___x_976_ = _args[2];
lean_object* v___x_977_ = _args[3];
lean_object* v_instImplicit_978_ = _args[4];
lean_object* v___x_979_ = _args[5];
lean_object* v_params_980_ = _args[6];
lean_object* v_self_981_ = _args[7];
lean_object* v_a_982_ = _args[8];
lean_object* v___x_983_ = _args[9];
lean_object* v_n_984_ = _args[10];
lean_object* v___x_985_ = _args[11];
lean_object* v_a_986_ = _args[12];
lean_object* v_a_987_ = _args[13];
lean_object* v_b_988_ = _args[14];
lean_object* v___y_989_ = _args[15];
lean_object* v___y_990_ = _args[16];
lean_object* v___y_991_ = _args[17];
lean_object* v___y_992_ = _args[18];
lean_object* v___y_993_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_994_; uint8_t v_a_18080__boxed_995_; lean_object* v_res_996_; 
v_instImplicit_boxed_994_ = lean_unbox(v_instImplicit_978_);
v_a_18080__boxed_995_ = lean_unbox(v_a_986_);
v_res_996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_974_, v_projDecls_975_, v___x_976_, v___x_977_, v_instImplicit_boxed_994_, v___x_979_, v_params_980_, v_self_981_, v_a_982_, v___x_983_, v_n_984_, v___x_985_, v_a_18080__boxed_995_, v_a_987_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_projDecls_975_);
lean_dec(v_upperBound_974_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_997_, lean_object* v_as_998_, size_t v_sz_999_, size_t v_i_1000_, lean_object* v_b_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_1000_, v_sz_999_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_b_1001_);
return v___x_1007_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_array_uget_borrowed(v_as_998_, v_i_1000_);
v___x_1009_ = l_Lean_Expr_fvarId_x21(v_a_1008_);
lean_inc(v___x_1009_);
v___x_1010_ = l_Lean_FVarId_getDecl___redArg(v___x_1009_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_a_1013_; uint8_t v___y_1018_; uint8_t v___x_1021_; uint8_t v___x_1022_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1021_ = l_Lean_LocalDecl_binderInfo(v_a_1011_);
v___x_1022_ = l_Lean_BinderInfo_isInstImplicit(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = l_Lean_LocalDecl_type(v_a_1011_);
lean_dec(v_a_1011_);
v___x_1025_ = l_Lean_Expr_isOutParam(v___x_1024_);
lean_dec_ref(v___x_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = 0;
v___x_1027_ = l_Lean_LocalContext_setBinderInfo(v_b_1001_, v___x_1009_, v___x_1026_);
v_a_1013_ = v___x_1027_;
goto v___jp_1012_;
}
else
{
goto v___jp_1023_;
}
}
else
{
lean_dec(v_a_1011_);
goto v___jp_1023_;
}
v___jp_1012_:
{
size_t v___x_1014_; size_t v___x_1015_; 
v___x_1014_ = ((size_t)1ULL);
v___x_1015_ = lean_usize_add(v_i_1000_, v___x_1014_);
v_i_1000_ = v___x_1015_;
v_b_1001_ = v_a_1013_;
goto _start;
}
v___jp_1017_:
{
if (v___y_1018_ == 0)
{
lean_dec(v___x_1009_);
v_a_1013_ = v_b_1001_;
goto v___jp_1012_;
}
else
{
uint8_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = 1;
v___x_1020_ = l_Lean_LocalContext_setBinderInfo(v_b_1001_, v___x_1009_, v___x_1019_);
v_a_1013_ = v___x_1020_;
goto v___jp_1012_;
}
}
v___jp_1023_:
{
if (v___x_1022_ == 0)
{
v___y_1018_ = v___x_1022_;
goto v___jp_1017_;
}
else
{
v___y_1018_ = v_instImplicit_997_;
goto v___jp_1017_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___x_1009_);
lean_dec_ref(v_b_1001_);
v_a_1028_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1010_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1010_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1036_, lean_object* v_as_1037_, lean_object* v_sz_1038_, lean_object* v_i_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_instImplicit_boxed_1045_; size_t v_sz_boxed_1046_; size_t v_i_boxed_1047_; lean_object* v_res_1048_; 
v_instImplicit_boxed_1045_ = lean_unbox(v_instImplicit_1036_);
v_sz_boxed_1046_ = lean_unbox_usize(v_sz_1038_);
lean_dec(v_sz_1038_);
v_i_boxed_1047_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_res_1048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1045_, v_as_1037_, v_sz_boxed_1046_, v_i_boxed_1047_, v_b_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_as_1037_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1049_, uint8_t v_instImplicit_1050_, lean_object* v_projDecls_1051_, lean_object* v_toConstantVal_1052_, lean_object* v_numParams_1053_, lean_object* v___x_1054_, lean_object* v_n_1055_, lean_object* v_levelParams_1056_, uint8_t v_a_1057_, lean_object* v_ctorType_1058_, lean_object* v_self_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_lctx_1065_; lean_object* v___x_1066_; size_t v_sz_1067_; size_t v___x_1068_; lean_object* v___x_1069_; 
v_lctx_1065_ = lean_ctor_get(v___y_1060_, 2);
lean_inc_ref(v_self_1059_);
lean_inc_ref(v_params_1049_);
v___x_1066_ = lean_array_push(v_params_1049_, v_self_1059_);
v_sz_1067_ = lean_array_size(v_params_1049_);
v___x_1068_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1065_);
v___x_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1050_, v_params_1049_, v_sz_1067_, v___x_1068_, v_lctx_1065_, v___y_1060_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = lean_array_get_size(v_projDecls_1051_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1071_, v_projDecls_1051_, v_toConstantVal_1052_, v_numParams_1053_, v_instImplicit_1050_, v___x_1054_, v_params_1049_, v_self_1059_, v_a_1070_, v___x_1066_, v_n_1055_, v_levelParams_1056_, v_a_1057_, v___x_1072_, v_ctorType_1058_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1082_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1073_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1073_);
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
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___x_1066_);
lean_dec_ref(v_self_1059_);
lean_dec_ref(v_ctorType_1058_);
lean_dec(v_levelParams_1056_);
lean_dec(v_n_1055_);
lean_dec(v___x_1054_);
lean_dec(v_numParams_1053_);
lean_dec_ref(v_toConstantVal_1052_);
lean_dec_ref(v_params_1049_);
v_a_1091_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1069_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1069_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1099_, lean_object* v_instImplicit_1100_, lean_object* v_projDecls_1101_, lean_object* v_toConstantVal_1102_, lean_object* v_numParams_1103_, lean_object* v___x_1104_, lean_object* v_n_1105_, lean_object* v_levelParams_1106_, lean_object* v_a_1107_, lean_object* v_ctorType_1108_, lean_object* v_self_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v_instImplicit_boxed_1115_; uint8_t v_a_18222__boxed_1116_; lean_object* v_res_1117_; 
v_instImplicit_boxed_1115_ = lean_unbox(v_instImplicit_1100_);
v_a_18222__boxed_1116_ = lean_unbox(v_a_1107_);
v_res_1117_ = l_Lean_Meta_mkProjections___lam__0(v_params_1099_, v_instImplicit_boxed_1115_, v_projDecls_1101_, v_toConstantVal_1102_, v_numParams_1103_, v___x_1104_, v_n_1105_, v_levelParams_1106_, v_a_18222__boxed_1116_, v_ctorType_1108_, v_self_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v_projDecls_1101_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1127_, lean_object* v_projDecls_1128_, lean_object* v_toConstantVal_1129_, lean_object* v_numParams_1130_, lean_object* v___x_1131_, lean_object* v_n_1132_, lean_object* v_levelParams_1133_, uint8_t v_a_1134_, lean_object* v_params_1135_, lean_object* v_ctorType_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; uint8_t v___y_1149_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___f_1155_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1153_ = lean_box(v_instImplicit_1127_);
v___x_1154_ = lean_box(v_a_1134_);
lean_inc(v_n_1132_);
lean_inc(v___x_1131_);
lean_inc(v_numParams_1130_);
lean_inc_ref(v_params_1135_);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1155_, 0, v_params_1135_);
lean_closure_set(v___f_1155_, 1, v___x_1153_);
lean_closure_set(v___f_1155_, 2, v_projDecls_1128_);
lean_closure_set(v___f_1155_, 3, v_toConstantVal_1129_);
lean_closure_set(v___f_1155_, 4, v_numParams_1130_);
lean_closure_set(v___f_1155_, 5, v___x_1131_);
lean_closure_set(v___f_1155_, 6, v_n_1132_);
lean_closure_set(v___f_1155_, 7, v_levelParams_1133_);
lean_closure_set(v___f_1155_, 8, v___x_1154_);
lean_closure_set(v___f_1155_, 9, v_ctorType_1136_);
v___x_1161_ = lean_array_get_size(v_params_1135_);
v___x_1162_ = lean_nat_dec_eq(v___x_1161_, v_numParams_1130_);
lean_dec(v_numParams_1130_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v___f_1155_);
lean_dec_ref(v_params_1135_);
lean_dec(v___x_1131_);
v___x_1163_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1164_ = l_Lean_MessageData_ofConstName(v_n_1132_, v___x_1162_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1167_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1168_;
}
else
{
goto v___jp_1156_;
}
v___jp_1142_:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1151_ = 0;
v___x_1152_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1150_, v___y_1149_, v___y_1144_, v___y_1148_, v___x_1151_, v___y_1147_, v___y_1143_, v___y_1146_, v___y_1145_);
return v___x_1152_;
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = l_Lean_Expr_const___override(v_n_1132_, v___x_1131_);
v___x_1158_ = l_Lean_mkAppN(v___x_1157_, v_params_1135_);
lean_dec_ref(v_params_1135_);
if (v_instImplicit_1127_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 0;
v___y_1143_ = v___y_1138_;
v___y_1144_ = v___x_1158_;
v___y_1145_ = v___y_1140_;
v___y_1146_ = v___y_1139_;
v___y_1147_ = v___y_1137_;
v___y_1148_ = v___f_1155_;
v___y_1149_ = v___x_1159_;
goto v___jp_1142_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 3;
v___y_1143_ = v___y_1138_;
v___y_1144_ = v___x_1158_;
v___y_1145_ = v___y_1140_;
v___y_1146_ = v___y_1139_;
v___y_1147_ = v___y_1137_;
v___y_1148_ = v___f_1155_;
v___y_1149_ = v___x_1160_;
goto v___jp_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1169_, lean_object* v_projDecls_1170_, lean_object* v_toConstantVal_1171_, lean_object* v_numParams_1172_, lean_object* v___x_1173_, lean_object* v_n_1174_, lean_object* v_levelParams_1175_, lean_object* v_a_1176_, lean_object* v_params_1177_, lean_object* v_ctorType_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_instImplicit_boxed_1184_; uint8_t v_a_18326__boxed_1185_; lean_object* v_res_1186_; 
v_instImplicit_boxed_1184_ = lean_unbox(v_instImplicit_1169_);
v_a_18326__boxed_1185_ = lean_unbox(v_a_1176_);
v_res_1186_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1184_, v_projDecls_1170_, v_toConstantVal_1171_, v_numParams_1172_, v___x_1173_, v_n_1174_, v_levelParams_1175_, v_a_18326__boxed_1185_, v_params_1177_, v_ctorType_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = l_List_reverse___redArg(v_a_1188_);
return v___x_1189_;
}
else
{
lean_object* v_head_1190_; lean_object* v_tail_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
v_head_1190_ = lean_ctor_get(v_a_1187_, 0);
v_tail_1191_ = lean_ctor_get(v_a_1187_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_a_1187_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v_a_1187_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_tail_1191_);
lean_inc(v_head_1190_);
lean_dec(v_a_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_mkLevelParam(v_head_1190_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_a_1188_);
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_a_1188_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v_a_1187_ = v_tail_1191_;
v_a_1188_ = v___x_1197_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_instMonadEIO(lean_box(0));
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_toApplicative_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1275_; 
v___x_1212_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
v_toApplicative_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1213_, 1);
lean_dec(v_unused_1276_);
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1275_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_toApplicative_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1275_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_toFunctor_1218_; lean_object* v_toSeq_1219_; lean_object* v_toSeqLeft_1220_; lean_object* v_toSeqRight_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1273_; 
v_toFunctor_1218_ = lean_ctor_get(v_toApplicative_1214_, 0);
v_toSeq_1219_ = lean_ctor_get(v_toApplicative_1214_, 2);
v_toSeqLeft_1220_ = lean_ctor_get(v_toApplicative_1214_, 3);
v_toSeqRight_1221_ = lean_ctor_get(v_toApplicative_1214_, 4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_toApplicative_1214_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_toApplicative_1214_, 1);
lean_dec(v_unused_1274_);
v___x_1223_ = v_toApplicative_1214_;
v_isShared_1224_ = v_isSharedCheck_1273_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_toSeqRight_1221_);
lean_inc(v_toSeqLeft_1220_);
lean_inc(v_toSeq_1219_);
lean_inc(v_toFunctor_1218_);
lean_dec(v_toApplicative_1214_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1273_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1234_; 
v___f_1225_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1226_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1218_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toFunctor_1218_);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toFunctor_1218_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___f_1227_);
lean_ctor_set(v___x_1229_, 1, v___f_1228_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toSeqRight_1221_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toSeqLeft_1220_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toSeq_1219_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v___f_1230_);
lean_ctor_set(v___x_1223_, 3, v___f_1231_);
lean_ctor_set(v___x_1223_, 2, v___f_1232_);
lean_ctor_set(v___x_1223_, 1, v___f_1225_);
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1234_ = v___x_1223_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___f_1225_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v___f_1232_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___f_1231_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___f_1230_);
v___x_1234_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___f_1226_);
lean_ctor_set(v___x_1216_, 0, v___x_1234_);
v___x_1236_ = v___x_1216_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___f_1226_);
v___x_1236_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v_toApplicative_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1269_; 
v___x_1237_ = l_StateRefT_x27_instMonad___redArg(v___x_1236_);
v_toApplicative_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1237_, 1);
lean_dec(v_unused_1270_);
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1269_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_toApplicative_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1269_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_toFunctor_1242_; lean_object* v_toSeq_1243_; lean_object* v_toSeqLeft_1244_; lean_object* v_toSeqRight_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1267_; 
v_toFunctor_1242_ = lean_ctor_get(v_toApplicative_1238_, 0);
v_toSeq_1243_ = lean_ctor_get(v_toApplicative_1238_, 2);
v_toSeqLeft_1244_ = lean_ctor_get(v_toApplicative_1238_, 3);
v_toSeqRight_1245_ = lean_ctor_get(v_toApplicative_1238_, 4);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_toApplicative_1238_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v_toApplicative_1238_, 1);
lean_dec(v_unused_1268_);
v___x_1247_ = v_toApplicative_1238_;
v_isShared_1248_ = v_isSharedCheck_1267_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_toSeqRight_1245_);
lean_inc(v_toSeqLeft_1244_);
lean_inc(v_toSeq_1243_);
lean_inc(v_toFunctor_1242_);
lean_dec(v_toApplicative_1238_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1267_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; lean_object* v___f_1254_; lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___x_1258_; 
v___f_1249_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1250_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1242_);
v___f_1251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1251_, 0, v_toFunctor_1242_);
v___f_1252_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1252_, 0, v_toFunctor_1242_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___f_1251_);
lean_ctor_set(v___x_1253_, 1, v___f_1252_);
v___f_1254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1254_, 0, v_toSeqRight_1245_);
v___f_1255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1255_, 0, v_toSeqLeft_1244_);
v___f_1256_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1256_, 0, v_toSeq_1243_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 4, v___f_1254_);
lean_ctor_set(v___x_1247_, 3, v___f_1255_);
lean_ctor_set(v___x_1247_, 2, v___f_1256_);
lean_ctor_set(v___x_1247_, 1, v___f_1249_);
lean_ctor_set(v___x_1247_, 0, v___x_1253_);
v___x_1258_ = v___x_1247_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___f_1249_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v___f_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v___f_1255_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v___f_1254_);
v___x_1258_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 1, v___f_1250_);
lean_ctor_set(v___x_1240_, 0, v___x_1258_);
v___x_1260_ = v___x_1240_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___f_1250_);
v___x_1260_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_13361__overap_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = l_instInhabitedOfMonad___redArg(v___x_1260_, v___x_1261_);
v___x_13361__overap_1263_ = lean_panic_fn_borrowed(v___x_1262_, v_msg_1206_);
lean_dec(v___x_1262_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
v___x_1264_ = lean_apply_5(v___x_13361__overap_1263_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, lean_box(0));
return v___x_1264_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1290_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1291_ = lean_unsigned_to_nat(11u);
v___x_1292_ = lean_unsigned_to_nat(122u);
v___x_1293_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1294_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1295_ = l_mkPanicMessageWithDecl(v___x_1294_, v___x_1293_, v___x_1292_, v___x_1291_, v___x_1290_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1310_; lean_object* v_env_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_st_ref_get(v___y_1300_);
v_env_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_env_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = 0;
lean_inc(v_constName_1296_);
v___x_1313_ = l_Lean_Environment_findAsync_x3f(v_env_1311_, v_constName_1296_, v___x_1312_);
if (lean_obj_tag(v___x_1313_) == 1)
{
lean_object* v_val_1314_; uint8_t v_kind_1315_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v_kind_1315_ = lean_ctor_get_uint8(v_val_1314_, sizeof(void*)*3);
if (v_kind_1315_ == 6)
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1314_);
if (lean_obj_tag(v___x_1316_) == 6)
{
lean_object* v_val_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_constName_1296_);
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_val_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_val_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v___x_1316_);
v___x_1325_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1326_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1325_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
if (lean_obj_tag(v_a_1327_) == 0)
{
lean_del_object(v___x_1329_);
goto v___jp_1302_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; 
lean_dec(v_constName_1296_);
v_val_1331_ = lean_ctor_get(v_a_1327_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_a_1327_, 1);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_val_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_val_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_constName_1296_);
v_a_1336_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1326_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1326_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
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
}
else
{
lean_dec(v_val_1314_);
goto v___jp_1302_;
}
}
else
{
lean_dec(v___x_1313_);
goto v___jp_1302_;
}
v___jp_1302_:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1303_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1304_ = 0;
v___x_1305_ = l_Lean_MessageData_ofConstName(v_constName_1296_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1303_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1308_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_env_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_st_ref_get(v___y_1358_);
v_env_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_ref(v_env_1361_);
lean_dec(v___x_1360_);
lean_inc(v_constName_1354_);
v___x_1362_ = l_Lean_isInductiveCore_x3f(v_env_1361_, v_constName_1354_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1363_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1364_ = 0;
v___x_1365_ = l_Lean_MessageData_ofConstName(v_constName_1354_, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1363_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1368_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_constName_1354_);
v_val_1370_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1362_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_val_1370_);
lean_dec(v___x_1362_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 0);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_val_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1387_ = l_Lean_stringToMessageData(v___x_1386_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1390_ = l_Lean_stringToMessageData(v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1391_, lean_object* v___x_1392_, uint8_t v_instImplicit_1393_, lean_object* v_projDecls_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc(v_n_1391_);
v___x_1400_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1391_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1442_ = l_Lean_InductiveVal_numCtors(v_a_1401_);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_dec_eq(v___x_1442_, v___x_1443_);
lean_dec(v___x_1442_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_a_1401_);
lean_dec_ref(v_projDecls_1394_);
v___x_1445_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1446_ = l_Lean_MessageData_ofConstName(v_n_1391_, v___x_1444_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1449_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1450_;
}
else
{
v___y_1403_ = v___y_1395_;
v___y_1404_ = v___y_1396_;
v___y_1405_ = v___y_1397_;
v___y_1406_ = v___y_1398_;
goto v___jp_1402_;
}
v___jp_1402_:
{
lean_object* v_toConstantVal_1407_; lean_object* v_numParams_1408_; lean_object* v_ctors_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_toConstantVal_1407_ = lean_ctor_get(v_a_1401_, 0);
lean_inc_ref(v_toConstantVal_1407_);
v_numParams_1408_ = lean_ctor_get(v_a_1401_, 1);
lean_inc(v_numParams_1408_);
v_ctors_1409_ = lean_ctor_get(v_a_1401_, 4);
lean_inc(v_ctors_1409_);
lean_dec(v_a_1401_);
v___x_1410_ = l_List_head_x21___redArg(v___x_1392_, v_ctors_1409_);
lean_dec(v_ctors_1409_);
v___x_1411_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1410_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v_levelParams_1413_; lean_object* v_type_1414_; lean_object* v___x_1415_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v_levelParams_1413_ = lean_ctor_get(v_toConstantVal_1407_, 1);
lean_inc(v_levelParams_1413_);
v_type_1414_ = lean_ctor_get(v_toConstantVal_1407_, 2);
lean_inc_ref(v_type_1414_);
lean_dec_ref(v_toConstantVal_1407_);
v___x_1415_ = l_Lean_Meta_isPropFormerType(v_type_1414_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_toConstantVal_1416_; lean_object* v_a_1417_; lean_object* v_type_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___f_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v_toConstantVal_1416_ = lean_ctor_get(v_a_1412_, 0);
lean_inc_ref(v_toConstantVal_1416_);
lean_dec(v_a_1412_);
v_a_1417_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1415_, 1);
v_type_1418_ = lean_ctor_get(v_toConstantVal_1416_, 2);
lean_inc_ref(v_type_1418_);
v___x_1419_ = lean_box(0);
lean_inc(v_levelParams_1413_);
v___x_1420_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1413_, v___x_1419_);
v___x_1421_ = lean_box(v_instImplicit_1393_);
lean_inc(v_numParams_1408_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1422_, 0, v___x_1421_);
lean_closure_set(v___f_1422_, 1, v_projDecls_1394_);
lean_closure_set(v___f_1422_, 2, v_toConstantVal_1416_);
lean_closure_set(v___f_1422_, 3, v_numParams_1408_);
lean_closure_set(v___f_1422_, 4, v___x_1420_);
lean_closure_set(v___f_1422_, 5, v_n_1391_);
lean_closure_set(v___f_1422_, 6, v_levelParams_1413_);
lean_closure_set(v___f_1422_, 7, v_a_1417_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_numParams_1408_);
v___x_1424_ = 0;
v___x_1425_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1418_, v___x_1423_, v___f_1422_, v___x_1424_, v___x_1424_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1425_;
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_levelParams_1413_);
lean_dec(v_a_1412_);
lean_dec(v_numParams_1408_);
lean_dec_ref(v_projDecls_1394_);
lean_dec(v_n_1391_);
v_a_1426_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1415_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1415_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_numParams_1408_);
lean_dec_ref(v_toConstantVal_1407_);
lean_dec_ref(v_projDecls_1394_);
lean_dec(v_n_1391_);
v_a_1434_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1411_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1411_);
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
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_projDecls_1394_);
lean_dec(v_n_1391_);
v_a_1451_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1400_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1400_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1459_, lean_object* v___x_1460_, lean_object* v_instImplicit_1461_, lean_object* v_projDecls_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_instImplicit_boxed_1468_; lean_object* v_res_1469_; 
v_instImplicit_boxed_1468_ = lean_unbox(v_instImplicit_1461_);
v_res_1469_ = l_Lean_Meta_mkProjections___lam__2(v_n_1459_, v___x_1460_, v_instImplicit_boxed_1468_, v_projDecls_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___x_1460_);
return v_res_1469_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = lean_unsigned_to_nat(32u);
v___x_1474_ = lean_mk_empty_array_with_capacity(v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1476_ = ((size_t)5ULL);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_unsigned_to_nat(32u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
v___x_1480_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1481_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
lean_ctor_set(v___x_1481_, 2, v___x_1477_);
lean_ctor_set(v___x_1481_, 3, v___x_1477_);
lean_ctor_set_usize(v___x_1481_, 4, v___x_1476_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1482_ = lean_box(1);
v___x_1483_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1484_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
lean_ctor_set(v___x_1485_, 2, v___x_1482_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1488_, lean_object* v_projDecls_1489_, uint8_t v_instImplicit_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_box(v_instImplicit_1490_);
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1498_, 0, v_n_1488_);
lean_closure_set(v___f_1498_, 1, v___x_1496_);
lean_closure_set(v___f_1498_, 2, v___x_1497_);
lean_closure_set(v___f_1498_, 3, v_projDecls_1489_);
v___x_1499_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1500_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1501_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1499_, v___x_1500_, v___f_1498_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1502_, lean_object* v_projDecls_1503_, lean_object* v_instImplicit_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
uint8_t v_instImplicit_boxed_1510_; lean_object* v_res_1511_; 
v_instImplicit_boxed_1510_ = lean_unbox(v_instImplicit_1504_);
v_res_1511_ = l_Lean_Meta_mkProjections(v_n_1502_, v_projDecls_1503_, v_instImplicit_boxed_1510_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1512_, lean_object* v_as_1513_, size_t v_sz_1514_, size_t v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1512_, v_as_1513_, v_sz_1514_, v_i_1515_, v_b_1516_, v___y_1517_, v___y_1519_, v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1523_, lean_object* v_as_1524_, lean_object* v_sz_1525_, lean_object* v_i_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_instImplicit_boxed_1533_; size_t v_sz_boxed_1534_; size_t v_i_boxed_1535_; lean_object* v_res_1536_; 
v_instImplicit_boxed_1533_ = lean_unbox(v_instImplicit_1523_);
v_sz_boxed_1534_ = lean_unbox_usize(v_sz_1525_);
lean_dec(v_sz_1525_);
v_i_boxed_1535_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1533_, v_as_1524_, v_sz_boxed_1534_, v_i_boxed_1535_, v_b_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v_as_1524_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1537_, uint8_t v_s_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1537_, v_s_1538_, v___y_1540_, v___y_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1545_, lean_object* v_s_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
uint8_t v_s_boxed_1552_; lean_object* v_res_1553_; 
v_s_boxed_1552_ = lean_unbox(v_s_1546_);
v_res_1553_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1545_, v_s_boxed_1552_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1554_, lean_object* v_ref_1555_, lean_object* v_msg_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1555_, v_msg_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_ref_1564_, lean_object* v_msg_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1563_, v_ref_1564_, v_msg_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v_ref_1564_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1572_, lean_object* v_x_1573_, uint8_t v_isExporting_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1573_, v_isExporting_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_x_1582_, lean_object* v_isExporting_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_isExporting_boxed_1589_; lean_object* v_res_1590_; 
v_isExporting_boxed_1589_ = lean_unbox(v_isExporting_1583_);
v_res_1590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1581_, v_x_1582_, v_isExporting_boxed_1589_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1591_, lean_object* v_x_1592_, uint8_t v_when_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1592_, v_when_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_x_1601_, lean_object* v_when_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v_when_boxed_1608_; lean_object* v_res_1609_; 
v_when_boxed_1608_ = lean_unbox(v_when_1602_);
v_res_1609_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1600_, v_x_1601_, v_when_boxed_1608_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1610_, lean_object* v_projDecls_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, uint8_t v_instImplicit_1614_, lean_object* v___x_1615_, lean_object* v_params_1616_, lean_object* v_self_1617_, lean_object* v_a_1618_, lean_object* v___x_1619_, lean_object* v_n_1620_, lean_object* v___x_1621_, uint8_t v_a_1622_, lean_object* v_inst_1623_, lean_object* v_R_1624_, lean_object* v_a_1625_, lean_object* v_b_1626_, lean_object* v_c_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1610_, v_projDecls_1611_, v___x_1612_, v___x_1613_, v_instImplicit_1614_, v___x_1615_, v_params_1616_, v_self_1617_, v_a_1618_, v___x_1619_, v_n_1620_, v___x_1621_, v_a_1622_, v_a_1625_, v_b_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1634_ = _args[0];
lean_object* v_projDecls_1635_ = _args[1];
lean_object* v___x_1636_ = _args[2];
lean_object* v___x_1637_ = _args[3];
lean_object* v_instImplicit_1638_ = _args[4];
lean_object* v___x_1639_ = _args[5];
lean_object* v_params_1640_ = _args[6];
lean_object* v_self_1641_ = _args[7];
lean_object* v_a_1642_ = _args[8];
lean_object* v___x_1643_ = _args[9];
lean_object* v_n_1644_ = _args[10];
lean_object* v___x_1645_ = _args[11];
lean_object* v_a_1646_ = _args[12];
lean_object* v_inst_1647_ = _args[13];
lean_object* v_R_1648_ = _args[14];
lean_object* v_a_1649_ = _args[15];
lean_object* v_b_1650_ = _args[16];
lean_object* v_c_1651_ = _args[17];
lean_object* v___y_1652_ = _args[18];
lean_object* v___y_1653_ = _args[19];
lean_object* v___y_1654_ = _args[20];
lean_object* v___y_1655_ = _args[21];
lean_object* v___y_1656_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1657_; uint8_t v_a_19079__boxed_1658_; lean_object* v_res_1659_; 
v_instImplicit_boxed_1657_ = lean_unbox(v_instImplicit_1638_);
v_a_19079__boxed_1658_ = lean_unbox(v_a_1646_);
v_res_1659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1634_, v_projDecls_1635_, v___x_1636_, v___x_1637_, v_instImplicit_boxed_1657_, v___x_1639_, v_params_1640_, v_self_1641_, v_a_1642_, v___x_1643_, v_n_1644_, v___x_1645_, v_a_19079__boxed_1658_, v_inst_1647_, v_R_1648_, v_a_1649_, v_b_1650_, v_c_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_projDecls_1635_);
lean_dec(v_upperBound_1634_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1660_, uint8_t v_allowLevelAssignments_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1661_, v_k_1660_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1667_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1667_);
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
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1684_, lean_object* v_allowLevelAssignments_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1691_; lean_object* v_res_1692_; 
v_allowLevelAssignments_boxed_1691_ = lean_unbox(v_allowLevelAssignments_1685_);
v_res_1692_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1684_, v_allowLevelAssignments_boxed_1691_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1693_, lean_object* v_k_1694_, uint8_t v_allowLevelAssignments_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1694_, v_allowLevelAssignments_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1702_, lean_object* v_k_1703_, lean_object* v_allowLevelAssignments_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1710_; lean_object* v_res_1711_; 
v_allowLevelAssignments_boxed_1710_ = lean_unbox(v_allowLevelAssignments_1704_);
v_res_1711_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1702_, v_k_1703_, v_allowLevelAssignments_boxed_1710_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1712_, size_t v_sz_1713_, size_t v_i_1714_, lean_object* v_b_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_usize_dec_lt(v_i_1714_, v_sz_1713_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1715_);
return v___x_1722_;
}
else
{
lean_object* v_snd_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1778_; 
v_snd_1723_ = lean_ctor_get(v_b_1715_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_b_1715_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_b_1715_, 0);
lean_dec(v_unused_1779_);
v___x_1725_ = v_b_1715_;
v_isShared_1726_ = v_isSharedCheck_1778_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snd_1723_);
lean_dec(v_b_1715_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1778_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_array_1727_; lean_object* v_start_1728_; lean_object* v_stop_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v_array_1727_ = lean_ctor_get(v_snd_1723_, 0);
v_start_1728_ = lean_ctor_get(v_snd_1723_, 1);
v_stop_1729_ = lean_ctor_get(v_snd_1723_, 2);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_nat_dec_lt(v_start_1728_, v_stop_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1733_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1730_);
v___x_1733_ = v___x_1725_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_snd_1723_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1774_; 
lean_inc(v_stop_1729_);
lean_inc(v_start_1728_);
lean_inc_ref(v_array_1727_);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_snd_1723_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; 
v_unused_1775_ = lean_ctor_get(v_snd_1723_, 2);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_snd_1723_, 1);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_snd_1723_, 0);
lean_dec(v_unused_1777_);
v___x_1737_ = v_snd_1723_;
v_isShared_1738_ = v_isSharedCheck_1774_;
goto v_resetjp_1736_;
}
else
{
lean_dec(v_snd_1723_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1774_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_a_1739_ = lean_array_uget_borrowed(v_as_1712_, v_i_1714_);
v___x_1740_ = lean_array_fget_borrowed(v_array_1727_, v_start_1728_);
lean_inc(v___x_1740_);
lean_inc(v_a_1739_);
v___x_1741_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1739_, v___x_1740_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1765_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1744_ = v___x_1741_;
v_isShared_1745_ = v_isSharedCheck_1765_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1741_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1765_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_add(v_start_1728_, v___x_1746_);
lean_dec(v_start_1728_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1747_);
v___x_1749_ = v___x_1737_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_array_1727_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_stop_1729_);
v___x_1749_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_unbox(v_a_1742_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_a_1742_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1749_);
lean_ctor_set(v___x_1725_, 0, v___x_1751_);
v___x_1753_ = v___x_1725_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1749_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1753_);
v___x_1755_ = v___x_1744_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
else
{
lean_object* v___x_1759_; 
lean_del_object(v___x_1744_);
lean_dec(v_a_1742_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1749_);
lean_ctor_set(v___x_1725_, 0, v___x_1730_);
v___x_1759_ = v___x_1725_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1749_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
size_t v___x_1760_; size_t v___x_1761_; 
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1714_, v___x_1760_);
v_i_1714_ = v___x_1761_;
v_b_1715_ = v___x_1759_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_del_object(v___x_1737_);
lean_dec(v_stop_1729_);
lean_dec(v_start_1728_);
lean_dec_ref(v_array_1727_);
lean_del_object(v___x_1725_);
v_a_1766_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1741_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1741_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
size_t v_sz_boxed_1789_; size_t v_i_boxed_1790_; lean_object* v_res_1791_; 
v_sz_boxed_1789_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1780_, v_sz_boxed_1789_, v_i_boxed_1790_, v_b_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v_as_1780_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1792_, lean_object* v_params2_1793_, lean_object* v___x_1794_, lean_object* v_params1_1795_, uint8_t v___x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
if (v___x_1792_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec(v___x_1794_);
lean_dec_ref(v_params2_1793_);
v___x_1802_ = lean_box(v___x_1792_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; size_t v_sz_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = l_Array_toSubarray___redArg(v_params2_1793_, v___x_1804_, v___x_1794_);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1805_);
v_sz_1808_ = lean_array_size(v_params1_1795_);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1795_, v_sz_1808_, v___x_1809_, v___x_1807_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_fst_1815_; 
v_fst_1815_ = lean_ctor_get(v_a_1811_, 0);
lean_inc(v_fst_1815_);
lean_dec(v_a_1811_);
if (lean_obj_tag(v_fst_1815_) == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_box(v___x_1796_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1822_; 
v_val_1820_ = lean_ctor_get(v_fst_1815_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_fst_1815_, 1);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_val_1820_);
v___x_1822_ = v___x_1813_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_val_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1810_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1810_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1833_, lean_object* v_params2_1834_, lean_object* v___x_1835_, lean_object* v_params1_1836_, lean_object* v___x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v___x_2006__boxed_1843_; uint8_t v___x_2008__boxed_1844_; lean_object* v_res_1845_; 
v___x_2006__boxed_1843_ = lean_unbox(v___x_1833_);
v___x_2008__boxed_1844_ = lean_unbox(v___x_1837_);
v_res_1845_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2006__boxed_1843_, v_params2_1834_, v___x_1835_, v_params1_1836_, v___x_2008__boxed_1844_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec_ref(v_params1_1836_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1846_, lean_object* v_params2_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___y_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1853_ = lean_array_get_size(v_params1_1846_);
v___x_1854_ = lean_array_get_size(v_params2_1847_);
v___x_1855_ = lean_nat_dec_eq(v___x_1853_, v___x_1854_);
v___x_1856_ = 1;
v___x_1857_ = lean_box(v___x_1855_);
v___x_1858_ = lean_box(v___x_1856_);
v___y_1859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1859_, 0, v___x_1857_);
lean_closure_set(v___y_1859_, 1, v_params2_1847_);
lean_closure_set(v___y_1859_, 2, v___x_1854_);
lean_closure_set(v___y_1859_, 3, v_params1_1846_);
lean_closure_set(v___y_1859_, 4, v___x_1858_);
v___x_1860_ = 0;
v___x_1861_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1859_, v___x_1860_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1862_, lean_object* v_params2_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1862_, v_params2_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; lean_object* v_env_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = lean_st_ref_get(v___y_1871_);
v_env_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc_ref(v_env_1874_);
lean_dec(v___x_1873_);
v___x_1875_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1874_, v_declName_1870_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1877_, v___y_1878_);
lean_dec(v___y_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1881_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1894_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1895_; lean_object* v_dummy_1896_; 
v___x_1895_ = lean_box(0);
v_dummy_1896_ = l_Lean_Expr_sort___override(v___x_1895_);
return v_dummy_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1897_, lean_object* v_induct_1898_, lean_object* v_params_1899_, lean_object* v_idx_1900_, lean_object* v_e_1901_, lean_object* v_x_x3f_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
if (lean_obj_tag(v_e_1901_) == 11)
{
lean_object* v_typeName_1914_; lean_object* v_idx_1915_; lean_object* v_struct_1916_; uint8_t v___x_1963_; 
v_typeName_1914_ = lean_ctor_get(v_e_1901_, 0);
v_idx_1915_ = lean_ctor_get(v_e_1901_, 1);
v_struct_1916_ = lean_ctor_get(v_e_1901_, 2);
lean_inc_ref(v_struct_1916_);
v___x_1963_ = lean_nat_dec_eq(v_idx_1915_, v_idx_1900_);
if (v___x_1963_ == 0)
{
lean_dec_ref(v_struct_1916_);
lean_dec_ref_known(v_e_1901_, 3);
lean_dec_ref(v_params_1899_);
goto v___jp_1908_;
}
else
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_name_eq(v_induct_1898_, v_typeName_1914_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v_struct_1916_);
lean_dec_ref_known(v_e_1901_, 3);
lean_dec_ref(v_params_1899_);
goto v___jp_1908_;
}
else
{
if (lean_obj_tag(v_x_x3f_1902_) == 0)
{
goto v___jp_1917_;
}
else
{
lean_object* v_val_1965_; uint8_t v___x_1966_; 
v_val_1965_ = lean_ctor_get(v_x_x3f_1902_, 0);
v___x_1966_ = lean_expr_eqv(v_val_1965_, v_struct_1916_);
if (v___x_1966_ == 0)
{
lean_dec_ref(v_struct_1916_);
lean_dec_ref_known(v_e_1901_, 3);
lean_dec_ref(v_params_1899_);
goto v___jp_1908_;
}
else
{
goto v___jp_1917_;
}
}
}
}
v___jp_1917_:
{
lean_object* v___x_1918_; 
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1903_);
v___x_1918_ = lean_infer_type(v_e_1901_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1903_);
v___x_1920_ = lean_whnf(v_a_1919_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_dummy_1922_; lean_object* v_nargs_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v_dummy_1922_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1923_ = l_Lean_Expr_getAppNumArgs(v_a_1921_);
lean_inc(v_nargs_1923_);
v___x_1924_ = lean_mk_array(v_nargs_1923_, v_dummy_1922_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_sub(v_nargs_1923_, v___x_1925_);
lean_dec(v_nargs_1923_);
v___x_1927_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1921_, v___x_1924_, v___x_1926_);
v___x_1928_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1899_, v___x_1927_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1938_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1933_ == 0)
{
lean_del_object(v___x_1931_);
lean_dec_ref(v_struct_1916_);
goto v___jp_1908_;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_struct_1916_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
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
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_struct_1916_);
v_a_1939_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1928_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1928_);
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
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_struct_1916_);
lean_dec_ref(v_params_1899_);
v_a_1947_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1920_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1920_);
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
lean_dec_ref(v_struct_1916_);
lean_dec_ref(v_params_1899_);
v_a_1955_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1918_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1918_);
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
}
else
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Expr_getAppFn(v_e_1901_);
if (lean_obj_tag(v___x_1967_) == 4)
{
lean_object* v_declName_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2019_; 
v_declName_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_declName_1968_);
lean_dec_ref_known(v___x_1967_, 2);
v___x_1969_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1968_, v_a_1906_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2019_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2019_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___y_1975_; lean_object* v___y_1976_; 
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_object* v_val_2004_; lean_object* v_ctorName_2005_; lean_object* v_numParams_2006_; lean_object* v_i_2007_; uint8_t v___y_2009_; uint8_t v___x_2017_; 
v_val_2004_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v_a_1970_, 1);
v_ctorName_2005_ = lean_ctor_get(v_val_2004_, 0);
lean_inc(v_ctorName_2005_);
v_numParams_2006_ = lean_ctor_get(v_val_2004_, 1);
lean_inc(v_numParams_2006_);
v_i_2007_ = lean_ctor_get(v_val_2004_, 2);
lean_inc(v_i_2007_);
lean_dec(v_val_2004_);
v___x_2017_ = lean_name_eq(v_ctorName_2005_, v_ctor_1897_);
lean_dec(v_ctorName_2005_);
if (v___x_2017_ == 0)
{
lean_dec(v_i_2007_);
v___y_2009_ = v___x_2017_;
goto v___jp_2008_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_nat_dec_eq(v_i_2007_, v_idx_1900_);
lean_dec(v_i_2007_);
v___y_2009_ = v___x_2018_;
goto v___jp_2008_;
}
v___jp_2008_:
{
if (v___y_2009_ == 0)
{
lean_dec(v_numParams_2006_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1901_);
lean_dec_ref(v_params_1899_);
goto v___jp_1911_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2010_ = l_Lean_Expr_getAppNumArgs(v_e_1901_);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_nat_add(v_numParams_2006_, v___x_2011_);
lean_dec(v_numParams_2006_);
v___x_2013_ = lean_nat_dec_eq(v___x_2010_, v___x_2012_);
lean_dec(v___x_2012_);
lean_dec(v___x_2010_);
if (v___x_2013_ == 0)
{
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1901_);
lean_dec_ref(v_params_1899_);
goto v___jp_1911_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Expr_appArg_x21(v_e_1901_);
if (lean_obj_tag(v_x_x3f_1902_) == 0)
{
v___y_1975_ = v___x_2011_;
v___y_1976_ = v___x_2014_;
goto v___jp_1974_;
}
else
{
lean_object* v_val_2015_; uint8_t v___x_2016_; 
v_val_2015_ = lean_ctor_get(v_x_x3f_1902_, 0);
v___x_2016_ = lean_expr_eqv(v_val_2015_, v___x_2014_);
if (v___x_2016_ == 0)
{
lean_dec_ref(v___x_2014_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1901_);
lean_dec_ref(v_params_1899_);
goto v___jp_1911_;
}
else
{
v___y_1975_ = v___x_2011_;
v___y_1976_ = v___x_2014_;
goto v___jp_1974_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
lean_dec_ref(v_e_1901_);
lean_dec_ref(v_params_1899_);
goto v___jp_1911_;
}
v___jp_1974_:
{
lean_object* v___x_1977_; lean_object* v_dummy_1978_; lean_object* v_nargs_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = l_Lean_Expr_appFn_x21(v_e_1901_);
lean_dec_ref(v_e_1901_);
v_dummy_1978_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1979_ = l_Lean_Expr_getAppNumArgs(v___x_1977_);
lean_inc(v_nargs_1979_);
v___x_1980_ = lean_mk_array(v_nargs_1979_, v_dummy_1978_);
v___x_1981_ = lean_nat_sub(v_nargs_1979_, v___y_1975_);
lean_dec(v_nargs_1979_);
v___x_1982_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1977_, v___x_1980_, v___x_1981_);
v___x_1983_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1899_, v___x_1982_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1995_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_unbox(v_a_1984_);
lean_dec(v_a_1984_);
if (v___x_1988_ == 0)
{
lean_del_object(v___x_1986_);
lean_dec_ref(v___y_1976_);
lean_del_object(v___x_1972_);
goto v___jp_1911_;
}
else
{
lean_object* v___x_1990_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 1);
lean_ctor_set(v___x_1972_, 0, v___y_1976_);
v___x_1990_ = v___x_1972_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___y_1976_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1990_);
v___x_1992_ = v___x_1986_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___y_1976_);
lean_del_object(v___x_1972_);
v_a_1996_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1983_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1983_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1967_);
lean_dec_ref(v_e_1901_);
lean_dec_ref(v_params_1899_);
goto v___jp_1911_;
}
}
v___jp_1908_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
return v___x_1910_;
}
v___jp_1911_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2020_, lean_object* v_induct_2021_, lean_object* v_params_2022_, lean_object* v_idx_2023_, lean_object* v_e_2024_, lean_object* v_x_x3f_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2020_, v_induct_2021_, v_params_2022_, v_idx_2023_, v_e_2024_, v_x_x3f_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_x_x3f_2025_);
lean_dec(v_idx_2023_);
lean_dec(v_induct_2021_);
lean_dec(v_ctor_2020_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v_env_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2038_ = lean_st_ref_get(v___y_2036_);
v_env_2042_ = lean_ctor_get(v___x_2038_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2038_);
v___x_2043_ = 0;
v___x_2044_ = l_Lean_Environment_findAsync_x3f(v_env_2042_, v_constName_2032_, v___x_2043_);
if (lean_obj_tag(v___x_2044_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2064_; 
v_val_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2064_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_val_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2064_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
uint8_t v_kind_2049_; 
v_kind_2049_ = lean_ctor_get_uint8(v_val_2045_, sizeof(void*)*3);
if (v_kind_2049_ == 6)
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2045_);
if (lean_obj_tag(v___x_2050_) == 6)
{
lean_object* v_val_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2061_; 
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_val_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2061_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v_val_2051_);
v___x_2056_ = v___x_2047_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_val_2051_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v___x_2050_);
lean_del_object(v___x_2047_);
v___x_2062_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2063_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2062_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
return v___x_2063_;
}
}
else
{
lean_del_object(v___x_2047_);
lean_dec(v_val_2045_);
goto v___jp_2039_;
}
}
}
else
{
lean_dec(v___x_2044_);
goto v___jp_2039_;
}
v___jp_2039_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = lean_box(0);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2080_, lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v_declName_2083_, lean_object* v___x_2084_, lean_object* v___x_2085_, lean_object* v_a_2086_, lean_object* v_val_2087_, lean_object* v_a_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v_a_2088_, v_upperBound_2080_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
lean_dec(v_a_2088_);
lean_dec_ref(v___x_2085_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_b_2089_);
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref(v_b_2089_);
v___x_2097_ = l_Lean_instInhabitedExpr;
v___x_2098_ = lean_nat_add(v___x_2081_, v_a_2088_);
v___x_2099_ = lean_array_get_borrowed(v___x_2097_, v___x_2082_, v___x_2098_);
lean_dec(v___x_2098_);
lean_inc(v___x_2099_);
lean_inc_ref(v___x_2085_);
v___x_2100_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2083_, v___x_2084_, v___x_2085_, v_a_2088_, v___x_2099_, v_a_2086_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2119_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2119_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2119_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
if (lean_obj_tag(v_a_2101_) == 1)
{
lean_object* v_val_2105_; uint8_t v___x_2106_; 
v_val_2105_ = lean_ctor_get(v_a_2101_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_a_2101_, 1);
v___x_2106_ = lean_expr_eqv(v_val_2105_, v_val_2087_);
lean_dec(v_val_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_a_2088_);
lean_dec_ref(v___x_2085_);
v___x_2107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2107_);
v___x_2109_ = v___x_2103_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_del_object(v___x_2103_);
v___x_2111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_nat_add(v_a_2088_, v___x_2112_);
lean_dec(v_a_2088_);
v_a_2088_ = v___x_2113_;
v_b_2089_ = v___x_2111_;
goto _start;
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_a_2101_);
lean_dec(v_a_2088_);
lean_dec_ref(v___x_2085_);
v___x_2115_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2115_);
v___x_2117_ = v___x_2103_;
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
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2088_);
lean_dec_ref(v___x_2085_);
v_a_2120_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2100_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2100_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2128_, lean_object* v___x_2129_, lean_object* v___x_2130_, lean_object* v_declName_2131_, lean_object* v___x_2132_, lean_object* v___x_2133_, lean_object* v_a_2134_, lean_object* v_val_2135_, lean_object* v_a_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2128_, v___x_2129_, v___x_2130_, v_declName_2131_, v___x_2132_, v___x_2133_, v_a_2134_, v_val_2135_, v_a_2136_, v_b_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v_val_2135_);
lean_dec(v_a_2134_);
lean_dec(v___x_2132_);
lean_dec(v_declName_2131_);
lean_dec_ref(v___x_2130_);
lean_dec(v___x_2129_);
lean_dec(v_upperBound_2128_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2144_, lean_object* v_p_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Expr_getAppFn(v_e_2144_);
if (lean_obj_tag(v___x_2151_) == 4)
{
lean_object* v_declName_2152_; lean_object* v___x_2153_; 
v_declName_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_n(v_declName_2152_, 2);
lean_dec_ref_known(v___x_2151_, 2);
v___x_2153_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2152_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2226_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2226_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2226_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
if (lean_obj_tag(v_a_2154_) == 1)
{
lean_object* v_val_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2223_; 
v_val_2163_ = lean_ctor_get(v_a_2154_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2165_ = v_a_2154_;
v_isShared_2166_ = v_isSharedCheck_2223_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_val_2163_);
lean_dec(v_a_2154_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2223_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_induct_2167_; lean_object* v_numParams_2168_; lean_object* v_numFields_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_induct_2167_ = lean_ctor_get(v_val_2163_, 1);
lean_inc_n(v_induct_2167_, 2);
v_numParams_2168_ = lean_ctor_get(v_val_2163_, 3);
lean_inc(v_numParams_2168_);
v_numFields_2169_ = lean_ctor_get(v_val_2163_, 4);
lean_inc(v_numFields_2169_);
lean_dec(v_val_2163_);
v___x_2170_ = lean_apply_1(v_p_2145_, v_induct_2167_);
v___x_2171_ = lean_unbox(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_del_object(v___x_2156_);
lean_dec(v_declName_2152_);
lean_dec_ref(v_e_2144_);
v___x_2172_ = lean_box(0);
if (v_isShared_2166_ == 0)
{
lean_ctor_set_tag(v___x_2165_, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2172_);
v___x_2174_ = v___x_2165_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
else
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
lean_del_object(v___x_2165_);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_nat_dec_lt(v___x_2176_, v_numFields_2169_);
if (v___x_2177_ == 0)
{
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2152_);
lean_dec_ref(v_e_2144_);
goto v___jp_2158_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = l_Lean_Expr_getAppNumArgs(v_e_2144_);
v___x_2179_ = lean_nat_add(v_numParams_2168_, v_numFields_2169_);
v___x_2180_ = lean_nat_dec_eq(v___x_2178_, v___x_2179_);
lean_dec(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec(v___x_2178_);
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2152_);
lean_dec_ref(v_e_2144_);
goto v___jp_2158_;
}
else
{
lean_object* v___x_2181_; lean_object* v_dummy_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_del_object(v___x_2156_);
v___x_2181_ = l_Lean_instInhabitedExpr;
v_dummy_2182_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2178_);
v___x_2183_ = lean_mk_array(v___x_2178_, v_dummy_2182_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v___x_2178_, v___x_2184_);
lean_dec(v___x_2178_);
v___x_2186_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2144_, v___x_2183_, v___x_2185_);
lean_inc(v_numParams_2168_);
v___x_2187_ = l_Array_extract___redArg(v___x_2186_, v___x_2176_, v_numParams_2168_);
v___x_2188_ = lean_array_get(v___x_2181_, v___x_2186_, v_numParams_2168_);
v___x_2189_ = lean_box(0);
lean_inc_ref(v___x_2187_);
v___x_2190_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2152_, v_induct_2167_, v___x_2187_, v___x_2176_, v___x_2188_, v___x_2189_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2222_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2222_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2222_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_del_object(v___x_2193_);
v_val_2195_ = lean_ctor_get(v_a_2191_, 0);
v___x_2196_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2169_, v_numParams_2168_, v___x_2186_, v_declName_2152_, v_induct_2167_, v___x_2187_, v_a_2191_, v_val_2195_, v___x_2184_, v___x_2196_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2152_);
lean_dec_ref(v___x_2186_);
lean_dec(v_numParams_2168_);
lean_dec(v_numFields_2169_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2210_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_fst_2202_; 
v_fst_2202_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_fst_2202_);
lean_dec(v_a_2198_);
if (lean_obj_tag(v_fst_2202_) == 0)
{
lean_object* v___x_2204_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_a_2191_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2191_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
else
{
lean_object* v_val_2206_; lean_object* v___x_2208_; 
lean_dec_ref_known(v_a_2191_, 1);
v_val_2206_ = lean_ctor_get(v_fst_2202_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v_fst_2202_, 1);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v_val_2206_);
v___x_2208_ = v___x_2200_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_val_2206_);
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
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref_known(v_a_2191_, 1);
v_a_2211_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2197_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2197_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_dec(v_a_2191_);
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2152_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2189_);
v___x_2220_ = v___x_2193_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2189_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_dec_ref(v___x_2187_);
lean_dec_ref(v___x_2186_);
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2152_);
return v___x_2190_;
}
}
}
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_del_object(v___x_2156_);
lean_dec(v_a_2154_);
lean_dec(v_declName_2152_);
lean_dec_ref(v_p_2145_);
lean_dec_ref(v_e_2144_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
v___jp_2158_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_box(0);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2159_);
v___x_2161_ = v___x_2156_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
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
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_declName_2152_);
lean_dec_ref(v_p_2145_);
lean_dec_ref(v_e_2144_);
v_a_2227_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2153_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2153_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref(v___x_2151_);
lean_dec_ref(v_p_2145_);
lean_dec_ref(v_e_2144_);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2237_, lean_object* v_p_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Meta_etaStruct_x3f(v_e_2237_, v_p_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_declName_2248_, lean_object* v___x_2249_, lean_object* v___x_2250_, lean_object* v_a_2251_, lean_object* v_val_2252_, lean_object* v_inst_2253_, lean_object* v_R_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_, lean_object* v_c_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2245_, v___x_2246_, v___x_2247_, v_declName_2248_, v___x_2249_, v___x_2250_, v_a_2251_, v_val_2252_, v_a_2255_, v_b_2256_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2264_ = _args[0];
lean_object* v___x_2265_ = _args[1];
lean_object* v___x_2266_ = _args[2];
lean_object* v_declName_2267_ = _args[3];
lean_object* v___x_2268_ = _args[4];
lean_object* v___x_2269_ = _args[5];
lean_object* v_a_2270_ = _args[6];
lean_object* v_val_2271_ = _args[7];
lean_object* v_inst_2272_ = _args[8];
lean_object* v_R_2273_ = _args[9];
lean_object* v_a_2274_ = _args[10];
lean_object* v_b_2275_ = _args[11];
lean_object* v_c_2276_ = _args[12];
lean_object* v___y_2277_ = _args[13];
lean_object* v___y_2278_ = _args[14];
lean_object* v___y_2279_ = _args[15];
lean_object* v___y_2280_ = _args[16];
lean_object* v___y_2281_ = _args[17];
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2264_, v___x_2265_, v___x_2266_, v_declName_2267_, v___x_2268_, v___x_2269_, v_a_2270_, v_val_2271_, v_inst_2272_, v_R_2273_, v_a_2274_, v_b_2275_, v_c_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v_val_2271_);
lean_dec(v_a_2270_);
lean_dec(v___x_2268_);
lean_dec(v_declName_2267_);
lean_dec_ref(v___x_2266_);
lean_dec(v___x_2265_);
lean_dec(v_upperBound_2264_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = l_Lean_Expr_hasMVar(v_e_2283_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_e_2283_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v_mctx_2289_; lean_object* v___x_2290_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; lean_object* v___x_2293_; lean_object* v_cache_2294_; lean_object* v_zetaDeltaFVarIds_2295_; lean_object* v_postponed_2296_; lean_object* v_diag_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
v___x_2288_ = lean_st_ref_get(v___y_2284_);
v_mctx_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_ref(v_mctx_2289_);
lean_dec(v___x_2288_);
v___x_2290_ = l_Lean_instantiateMVarsCore(v_mctx_2289_, v_e_2283_);
v_fst_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_fst_2291_);
v_snd_2292_ = lean_ctor_get(v___x_2290_, 1);
lean_inc(v_snd_2292_);
lean_dec_ref(v___x_2290_);
v___x_2293_ = lean_st_ref_take(v___y_2284_);
v_cache_2294_ = lean_ctor_get(v___x_2293_, 1);
v_zetaDeltaFVarIds_2295_ = lean_ctor_get(v___x_2293_, 2);
v_postponed_2296_ = lean_ctor_get(v___x_2293_, 3);
v_diag_2297_ = lean_ctor_get(v___x_2293_, 4);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2293_, 0);
lean_dec(v_unused_2307_);
v___x_2299_ = v___x_2293_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_diag_2297_);
lean_inc(v_postponed_2296_);
lean_inc(v_zetaDeltaFVarIds_2295_);
lean_inc(v_cache_2294_);
lean_dec(v___x_2293_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v_snd_2292_);
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_snd_2292_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_cache_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_zetaDeltaFVarIds_2295_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_postponed_2296_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v_diag_2297_);
v___x_2302_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_st_ref_put(v___y_2284_, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_fst_2291_);
return v___x_2304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2308_, v___y_2309_);
lean_dec(v___y_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2312_, v___y_2314_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_x_2336_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2343_, lean_object* v_e_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_etaStruct_x3f(v_e_2344_, v_p_2343_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2370_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
if (lean_obj_tag(v_a_2351_) == 1)
{
lean_object* v_val_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2365_; 
v_val_2355_ = lean_ctor_get(v_a_2351_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_a_2351_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2357_ = v_a_2351_;
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_val_2355_);
lean_dec(v_a_2351_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set_tag(v___x_2357_, 0);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_val_2355_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2360_);
v___x_2362_ = v___x_2353_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec(v_a_2351_);
v___x_2366_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2366_);
v___x_2368_ = v___x_2353_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2350_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2350_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2379_, lean_object* v_e_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2379_, v_e_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2387_, lean_object* v_x_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_apply_1(v_x_2388_, lean_box(0));
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_x_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2396_, v_x_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2404_, lean_object* v_b_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_dec(v_b_2405_);
lean_dec_ref(v_a_2404_);
return v_x_2406_;
}
else
{
lean_object* v_key_2407_; lean_object* v_value_2408_; lean_object* v_tail_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2421_; 
v_key_2407_ = lean_ctor_get(v_x_2406_, 0);
v_value_2408_ = lean_ctor_get(v_x_2406_, 1);
v_tail_2409_ = lean_ctor_get(v_x_2406_, 2);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_x_2406_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2411_ = v_x_2406_;
v_isShared_2412_ = v_isSharedCheck_2421_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_tail_2409_);
lean_inc(v_value_2408_);
lean_inc(v_key_2407_);
lean_dec(v_x_2406_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2421_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
uint8_t v___x_2413_; 
v___x_2413_ = l_Lean_ExprStructEq_beq(v_key_2407_, v_a_2404_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2404_, v_b_2405_, v_tail_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 2, v___x_2414_);
v___x_2416_ = v___x_2411_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_key_2407_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_value_2408_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
else
{
lean_object* v___x_2419_; 
lean_dec(v_value_2408_);
lean_dec(v_key_2407_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v_b_2405_);
lean_ctor_set(v___x_2411_, 0, v_a_2404_);
v___x_2419_ = v___x_2411_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2404_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_b_2405_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_tail_2409_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2422_, lean_object* v_x_2423_){
_start:
{
if (lean_obj_tag(v_x_2423_) == 0)
{
return v_x_2422_;
}
else
{
lean_object* v_key_2424_; lean_object* v_value_2425_; lean_object* v_tail_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2449_; 
v_key_2424_ = lean_ctor_get(v_x_2423_, 0);
v_value_2425_ = lean_ctor_get(v_x_2423_, 1);
v_tail_2426_ = lean_ctor_get(v_x_2423_, 2);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_x_2423_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2428_ = v_x_2423_;
v_isShared_2429_ = v_isSharedCheck_2449_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_tail_2426_);
lean_inc(v_value_2425_);
lean_inc(v_key_2424_);
lean_dec(v_x_2423_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2449_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; uint64_t v___x_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; uint64_t v_fold_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; size_t v___x_2440_; size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2430_ = lean_array_get_size(v_x_2422_);
v___x_2431_ = l_Lean_ExprStructEq_hash(v_key_2424_);
v___x_2432_ = 32ULL;
v___x_2433_ = lean_uint64_shift_right(v___x_2431_, v___x_2432_);
v_fold_2434_ = lean_uint64_xor(v___x_2431_, v___x_2433_);
v___x_2435_ = 16ULL;
v___x_2436_ = lean_uint64_shift_right(v_fold_2434_, v___x_2435_);
v___x_2437_ = lean_uint64_xor(v_fold_2434_, v___x_2436_);
v___x_2438_ = lean_uint64_to_usize(v___x_2437_);
v___x_2439_ = lean_usize_of_nat(v___x_2430_);
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_sub(v___x_2439_, v___x_2440_);
v___x_2442_ = lean_usize_land(v___x_2438_, v___x_2441_);
v___x_2443_ = lean_array_uget_borrowed(v_x_2422_, v___x_2442_);
lean_inc(v___x_2443_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 2, v___x_2443_);
v___x_2445_ = v___x_2428_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_key_2424_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_value_2425_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_array_uset(v_x_2422_, v___x_2442_, v___x_2445_);
v_x_2422_ = v___x_2446_;
v_x_2423_ = v_tail_2426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2450_, lean_object* v_source_2451_, lean_object* v_target_2452_){
_start:
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = lean_array_get_size(v_source_2451_);
v___x_2454_ = lean_nat_dec_lt(v_i_2450_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_dec_ref(v_source_2451_);
lean_dec(v_i_2450_);
return v_target_2452_;
}
else
{
lean_object* v_es_2455_; lean_object* v___x_2456_; lean_object* v_source_2457_; lean_object* v_target_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_es_2455_ = lean_array_fget(v_source_2451_, v_i_2450_);
v___x_2456_ = lean_box(0);
v_source_2457_ = lean_array_fset(v_source_2451_, v_i_2450_, v___x_2456_);
v_target_2458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2452_, v_es_2455_);
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_nat_add(v_i_2450_, v___x_2459_);
lean_dec(v_i_2450_);
v_i_2450_ = v___x_2460_;
v_source_2451_ = v_source_2457_;
v_target_2452_ = v_target_2458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_nbuckets_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2463_ = lean_array_get_size(v_data_2462_);
v___x_2464_ = lean_unsigned_to_nat(2u);
v_nbuckets_2465_ = lean_nat_mul(v___x_2463_, v___x_2464_);
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_mk_array(v_nbuckets_2465_, v___x_2467_);
v___x_2469_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2466_, v_data_2462_, v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = 0;
return v___x_2472_;
}
else
{
lean_object* v_key_2473_; lean_object* v_tail_2474_; uint8_t v___x_2475_; 
v_key_2473_ = lean_ctor_get(v_x_2471_, 0);
v_tail_2474_ = lean_ctor_get(v_x_2471_, 2);
v___x_2475_ = l_Lean_ExprStructEq_beq(v_key_2473_, v_a_2470_);
if (v___x_2475_ == 0)
{
v_x_2471_ = v_tail_2474_;
goto _start;
}
else
{
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2477_, lean_object* v_x_2478_){
_start:
{
uint8_t v_res_2479_; lean_object* v_r_2480_; 
v_res_2479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2477_, v_x_2478_);
lean_dec(v_x_2478_);
lean_dec_ref(v_a_2477_);
v_r_2480_ = lean_box(v_res_2479_);
return v_r_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2481_, lean_object* v_a_2482_, lean_object* v_b_2483_){
_start:
{
lean_object* v_size_2484_; lean_object* v_buckets_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2528_; 
v_size_2484_ = lean_ctor_get(v_m_2481_, 0);
v_buckets_2485_ = lean_ctor_get(v_m_2481_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_m_2481_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2487_ = v_m_2481_;
v_isShared_2488_ = v_isSharedCheck_2528_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_buckets_2485_);
lean_inc(v_size_2484_);
lean_dec(v_m_2481_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2528_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; uint64_t v_fold_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; lean_object* v_bkt_2502_; uint8_t v___x_2503_; 
v___x_2489_ = lean_array_get_size(v_buckets_2485_);
v___x_2490_ = l_Lean_ExprStructEq_hash(v_a_2482_);
v___x_2491_ = 32ULL;
v___x_2492_ = lean_uint64_shift_right(v___x_2490_, v___x_2491_);
v_fold_2493_ = lean_uint64_xor(v___x_2490_, v___x_2492_);
v___x_2494_ = 16ULL;
v___x_2495_ = lean_uint64_shift_right(v_fold_2493_, v___x_2494_);
v___x_2496_ = lean_uint64_xor(v_fold_2493_, v___x_2495_);
v___x_2497_ = lean_uint64_to_usize(v___x_2496_);
v___x_2498_ = lean_usize_of_nat(v___x_2489_);
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_sub(v___x_2498_, v___x_2499_);
v___x_2501_ = lean_usize_land(v___x_2497_, v___x_2500_);
v_bkt_2502_ = lean_array_uget_borrowed(v_buckets_2485_, v___x_2501_);
v___x_2503_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2482_, v_bkt_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v_size_x27_2505_; lean_object* v___x_2506_; lean_object* v_buckets_x27_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2504_ = lean_unsigned_to_nat(1u);
v_size_x27_2505_ = lean_nat_add(v_size_2484_, v___x_2504_);
lean_dec(v_size_2484_);
lean_inc(v_bkt_2502_);
v___x_2506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2482_);
lean_ctor_set(v___x_2506_, 1, v_b_2483_);
lean_ctor_set(v___x_2506_, 2, v_bkt_2502_);
v_buckets_x27_2507_ = lean_array_uset(v_buckets_2485_, v___x_2501_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(4u);
v___x_2509_ = lean_nat_mul(v_size_x27_2505_, v___x_2508_);
v___x_2510_ = lean_unsigned_to_nat(3u);
v___x_2511_ = lean_nat_div(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_array_get_size(v_buckets_x27_2507_);
v___x_2513_ = lean_nat_dec_le(v___x_2511_, v___x_2512_);
lean_dec(v___x_2511_);
if (v___x_2513_ == 0)
{
lean_object* v_val_2514_; lean_object* v___x_2516_; 
v_val_2514_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2507_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v_val_2514_);
lean_ctor_set(v___x_2487_, 0, v_size_x27_2505_);
v___x_2516_ = v___x_2487_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_size_x27_2505_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_val_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
else
{
lean_object* v___x_2519_; 
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v_buckets_x27_2507_);
lean_ctor_set(v___x_2487_, 0, v_size_x27_2505_);
v___x_2519_ = v___x_2487_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_x27_2505_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_buckets_x27_2507_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v___x_2521_; lean_object* v_buckets_x27_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_inc(v_bkt_2502_);
v___x_2521_ = lean_box(0);
v_buckets_x27_2522_ = lean_array_uset(v_buckets_2485_, v___x_2501_, v___x_2521_);
v___x_2523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2482_, v_b_2483_, v_bkt_2502_);
v___x_2524_ = lean_array_uset(v_buckets_x27_2522_, v___x_2501_, v___x_2523_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v___x_2524_);
v___x_2526_ = v___x_2487_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_size_2484_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2529_, lean_object* v_e_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_st_ref_take(v_a_2529_);
v___x_2534_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2533_, v_e_2530_, v_a_2531_);
v___x_2535_ = lean_st_ref_put(v_a_2529_, v___x_2534_);
v___x_2536_ = lean_box(0);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2537_, lean_object* v_e_2538_, lean_object* v_a_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2537_, v_e_2538_, v_a_2539_);
lean_dec(v_a_2537_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2542_, lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_apply_1(v_x_2543_, lean_box(0));
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2551_, v_x_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2559_, lean_object* v_x_2560_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_box(0);
return v___x_2561_;
}
else
{
lean_object* v_key_2562_; lean_object* v_value_2563_; lean_object* v_tail_2564_; uint8_t v___x_2565_; 
v_key_2562_ = lean_ctor_get(v_x_2560_, 0);
v_value_2563_ = lean_ctor_get(v_x_2560_, 1);
v_tail_2564_ = lean_ctor_get(v_x_2560_, 2);
v___x_2565_ = l_Lean_ExprStructEq_beq(v_key_2562_, v_a_2559_);
if (v___x_2565_ == 0)
{
v_x_2560_ = v_tail_2564_;
goto _start;
}
else
{
lean_object* v___x_2567_; 
lean_inc(v_value_2563_);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_value_2563_);
return v___x_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2568_, lean_object* v_x_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2568_, v_x_2569_);
lean_dec(v_x_2569_);
lean_dec_ref(v_a_2568_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_buckets_2573_; lean_object* v___x_2574_; uint64_t v___x_2575_; uint64_t v___x_2576_; uint64_t v___x_2577_; uint64_t v_fold_2578_; uint64_t v___x_2579_; uint64_t v___x_2580_; uint64_t v___x_2581_; size_t v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_buckets_2573_ = lean_ctor_get(v_m_2571_, 1);
v___x_2574_ = lean_array_get_size(v_buckets_2573_);
v___x_2575_ = l_Lean_ExprStructEq_hash(v_a_2572_);
v___x_2576_ = 32ULL;
v___x_2577_ = lean_uint64_shift_right(v___x_2575_, v___x_2576_);
v_fold_2578_ = lean_uint64_xor(v___x_2575_, v___x_2577_);
v___x_2579_ = 16ULL;
v___x_2580_ = lean_uint64_shift_right(v_fold_2578_, v___x_2579_);
v___x_2581_ = lean_uint64_xor(v_fold_2578_, v___x_2580_);
v___x_2582_ = lean_uint64_to_usize(v___x_2581_);
v___x_2583_ = lean_usize_of_nat(v___x_2574_);
v___x_2584_ = ((size_t)1ULL);
v___x_2585_ = lean_usize_sub(v___x_2583_, v___x_2584_);
v___x_2586_ = lean_usize_land(v___x_2582_, v___x_2585_);
v___x_2587_ = lean_array_uget_borrowed(v_buckets_2573_, v___x_2586_);
v___x_2588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2572_, v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2589_, v_a_2590_);
lean_dec_ref(v_a_2590_);
lean_dec_ref(v_m_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2592_, lean_object* v___y_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2593_);
v___x_2600_ = lean_apply_7(v_k_2592_, v_b_2594_, v___y_2593_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, lean_box(0));
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2601_, lean_object* v___y_2602_, lean_object* v_b_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2601_, v___y_2602_, v_b_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2602_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2610_, uint8_t v_bi_2611_, lean_object* v_type_2612_, lean_object* v_k_2613_, uint8_t v_kind_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___f_2621_; lean_object* v___x_2622_; 
lean_inc(v___y_2615_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2621_, 0, v_k_2613_);
lean_closure_set(v___f_2621_, 1, v___y_2615_);
v___x_2622_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2610_, v_bi_2611_, v_type_2612_, v___f_2621_, v_kind_2614_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2622_) == 0)
{
return v___x_2622_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2631_, lean_object* v_bi_2632_, lean_object* v_type_2633_, lean_object* v_k_2634_, lean_object* v_kind_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v_bi_boxed_2642_; uint8_t v_kind_boxed_2643_; lean_object* v_res_2644_; 
v_bi_boxed_2642_ = lean_unbox(v_bi_2632_);
v_kind_boxed_2643_ = lean_unbox(v_kind_2635_);
v_res_2644_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2631_, v_bi_boxed_2642_, v_type_2633_, v_k_2634_, v_kind_boxed_2643_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2645_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2659_, lean_object* v_type_2660_, lean_object* v_val_2661_, lean_object* v_k_2662_, uint8_t v_nondep_2663_, uint8_t v_kind_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___f_2671_; lean_object* v___x_2672_; 
lean_inc(v___y_2665_);
v___f_2671_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2671_, 0, v_k_2662_);
lean_closure_set(v___f_2671_, 1, v___y_2665_);
v___x_2672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2659_, v_type_2660_, v_val_2661_, v___f_2671_, v_nondep_2663_, v_kind_2664_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2672_) == 0)
{
return v___x_2672_;
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2681_, lean_object* v_type_2682_, lean_object* v_val_2683_, lean_object* v_k_2684_, lean_object* v_nondep_2685_, lean_object* v_kind_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
uint8_t v_nondep_boxed_2693_; uint8_t v_kind_boxed_2694_; lean_object* v_res_2695_; 
v_nondep_boxed_2693_ = lean_unbox(v_nondep_2685_);
v_kind_boxed_2694_ = lean_unbox(v_kind_2686_);
v_res_2695_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2681_, v_type_2682_, v_val_2683_, v_k_2684_, v_nondep_boxed_2693_, v_kind_boxed_2694_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
return v_res_2695_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = l_Lean_maxRecDepthErrorMessage;
v___x_2702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2704_ = l_Lean_MessageData_ofFormat(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2706_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2707_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2708_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_ref_2708_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___y_2724_; lean_object* v_toCold_2733_; lean_object* v_options_2734_; lean_object* v_currRecDepth_2735_; lean_object* v_maxRecDepth_2736_; lean_object* v_ref_2737_; lean_object* v_currNamespace_2738_; lean_object* v_openDecls_2739_; lean_object* v_initHeartbeats_2740_; lean_object* v_maxHeartbeats_2741_; lean_object* v_currMacroScope_2742_; uint8_t v_diag_2743_; uint8_t v_suppressElabErrors_2744_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_toCold_2733_ = lean_ctor_get(v___y_2720_, 0);
v_options_2734_ = lean_ctor_get(v___y_2720_, 1);
v_currRecDepth_2735_ = lean_ctor_get(v___y_2720_, 2);
v_maxRecDepth_2736_ = lean_ctor_get(v___y_2720_, 3);
v_ref_2737_ = lean_ctor_get(v___y_2720_, 4);
v_currNamespace_2738_ = lean_ctor_get(v___y_2720_, 5);
v_openDecls_2739_ = lean_ctor_get(v___y_2720_, 6);
v_initHeartbeats_2740_ = lean_ctor_get(v___y_2720_, 7);
v_maxHeartbeats_2741_ = lean_ctor_get(v___y_2720_, 8);
v_currMacroScope_2742_ = lean_ctor_get(v___y_2720_, 9);
v_diag_2743_ = lean_ctor_get_uint8(v___y_2720_, sizeof(void*)*10);
v_suppressElabErrors_2744_ = lean_ctor_get_uint8(v___y_2720_, sizeof(void*)*10 + 1);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_nat_dec_eq(v_maxRecDepth_2736_, v___x_2750_);
if (v___x_2751_ == 0)
{
uint8_t v___x_2752_; 
v___x_2752_ = lean_nat_dec_eq(v_currRecDepth_2735_, v_maxRecDepth_2736_);
if (v___x_2752_ == 0)
{
goto v___jp_2745_;
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref(v_x_2716_);
lean_inc(v_ref_2737_);
v___x_2753_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2737_);
v___y_2724_ = v___x_2753_;
goto v___jp_2723_;
}
}
else
{
goto v___jp_2745_;
}
v___jp_2723_:
{
if (lean_obj_tag(v___y_2724_) == 0)
{
return v___y_2724_;
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___y_2724_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___y_2724_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___y_2724_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___y_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
v___jp_2745_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_nat_add(v_currRecDepth_2735_, v___x_2746_);
lean_inc(v_currMacroScope_2742_);
lean_inc(v_maxHeartbeats_2741_);
lean_inc(v_initHeartbeats_2740_);
lean_inc(v_openDecls_2739_);
lean_inc(v_currNamespace_2738_);
lean_inc(v_ref_2737_);
lean_inc(v_maxRecDepth_2736_);
lean_inc_ref(v_options_2734_);
lean_inc_ref(v_toCold_2733_);
v___x_2748_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2748_, 0, v_toCold_2733_);
lean_ctor_set(v___x_2748_, 1, v_options_2734_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
lean_ctor_set(v___x_2748_, 3, v_maxRecDepth_2736_);
lean_ctor_set(v___x_2748_, 4, v_ref_2737_);
lean_ctor_set(v___x_2748_, 5, v_currNamespace_2738_);
lean_ctor_set(v___x_2748_, 6, v_openDecls_2739_);
lean_ctor_set(v___x_2748_, 7, v_initHeartbeats_2740_);
lean_ctor_set(v___x_2748_, 8, v_maxHeartbeats_2741_);
lean_ctor_set(v___x_2748_, 9, v_currMacroScope_2742_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*10, v_diag_2743_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*10 + 1, v_suppressElabErrors_2744_);
lean_inc(v___y_2721_);
lean_inc(v___y_2719_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
v___x_2749_ = lean_apply_6(v_x_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___x_2748_, v___y_2721_, lean_box(0));
v___y_2724_ = v___x_2749_;
goto v___jp_2723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2765_, lean_object* v_pre_2766_, lean_object* v_post_2767_, uint8_t v_usedLetOnly_2768_, uint8_t v_skipConstInApp_2769_, uint8_t v_skipInstances_2770_, lean_object* v_body_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_array_push(v_fvars_2765_, v_x_2772_);
v___x_2780_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2766_, v_post_2767_, v_usedLetOnly_2768_, v_skipConstInApp_2769_, v_skipInstances_2770_, v___x_2779_, v_body_2771_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2781_, lean_object* v_pre_2782_, lean_object* v_post_2783_, lean_object* v_usedLetOnly_2784_, lean_object* v_skipConstInApp_2785_, lean_object* v_skipInstances_2786_, lean_object* v_body_2787_, lean_object* v_x_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v_usedLetOnly_boxed_2795_; uint8_t v_skipConstInApp_boxed_2796_; uint8_t v_skipInstances_boxed_2797_; lean_object* v_res_2798_; 
v_usedLetOnly_boxed_2795_ = lean_unbox(v_usedLetOnly_2784_);
v_skipConstInApp_boxed_2796_ = lean_unbox(v_skipConstInApp_2785_);
v_skipInstances_boxed_2797_ = lean_unbox(v_skipInstances_2786_);
v_res_2798_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2781_, v_pre_2782_, v_post_2783_, v_usedLetOnly_boxed_2795_, v_skipConstInApp_boxed_2796_, v_skipInstances_boxed_2797_, v_body_2787_, v_x_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2799_, lean_object* v_post_2800_, uint8_t v_usedLetOnly_2801_, uint8_t v_skipConstInApp_2802_, uint8_t v_skipInstances_2803_, lean_object* v_e_2804_, lean_object* v_a_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
lean_inc_ref(v_post_2800_);
lean_inc(v___y_2809_);
lean_inc_ref(v___y_2808_);
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc_ref(v_e_2804_);
v___x_2811_ = lean_apply_6(v_post_2800_, v_e_2804_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, lean_box(0));
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2830_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2830_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2830_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
switch(lean_obj_tag(v_a_2812_))
{
case 0:
{
lean_object* v_e_2816_; lean_object* v___x_2818_; 
lean_dec_ref(v_e_2804_);
lean_dec_ref(v_post_2800_);
lean_dec_ref(v_pre_2799_);
v_e_2816_ = lean_ctor_get(v_a_2812_, 0);
lean_inc_ref(v_e_2816_);
lean_dec_ref_known(v_a_2812_, 1);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_e_2816_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_e_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
case 1:
{
lean_object* v_e_2820_; lean_object* v___x_2821_; 
lean_del_object(v___x_2814_);
lean_dec_ref(v_e_2804_);
v_e_2820_ = lean_ctor_get(v_a_2812_, 0);
lean_inc_ref(v_e_2820_);
lean_dec_ref_known(v_a_2812_, 1);
v___x_2821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2799_, v_post_2800_, v_usedLetOnly_2801_, v_skipConstInApp_2802_, v_skipInstances_2803_, v_e_2820_, v_a_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
return v___x_2821_;
}
default: 
{
lean_object* v_e_x3f_2822_; 
lean_dec_ref(v_post_2800_);
lean_dec_ref(v_pre_2799_);
v_e_x3f_2822_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_e_x3f_2822_);
lean_dec_ref_known(v_a_2812_, 1);
if (lean_obj_tag(v_e_x3f_2822_) == 0)
{
lean_object* v___x_2824_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_e_2804_);
v___x_2824_ = v___x_2814_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_e_2804_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
else
{
lean_object* v_val_2826_; lean_object* v___x_2828_; 
lean_dec_ref(v_e_2804_);
v_val_2826_ = lean_ctor_get(v_e_x3f_2822_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_e_x3f_2822_, 1);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_val_2826_);
v___x_2828_ = v___x_2814_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_val_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v_e_2804_);
lean_dec_ref(v_post_2800_);
lean_dec_ref(v_pre_2799_);
v_a_2831_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2811_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2811_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2839_, lean_object* v_post_2840_, uint8_t v_usedLetOnly_2841_, uint8_t v_skipConstInApp_2842_, uint8_t v_skipInstances_2843_, lean_object* v_fvars_2844_, lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
if (lean_obj_tag(v_e_2845_) == 6)
{
lean_object* v_binderName_2852_; lean_object* v_binderType_2853_; lean_object* v_body_2854_; uint8_t v_binderInfo_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_binderName_2852_ = lean_ctor_get(v_e_2845_, 0);
lean_inc(v_binderName_2852_);
v_binderType_2853_ = lean_ctor_get(v_e_2845_, 1);
lean_inc_ref(v_binderType_2853_);
v_body_2854_ = lean_ctor_get(v_e_2845_, 2);
lean_inc_ref(v_body_2854_);
v_binderInfo_2855_ = lean_ctor_get_uint8(v_e_2845_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2845_, 3);
v___x_2856_ = lean_expr_instantiate_rev(v_binderType_2853_, v_fvars_2844_);
lean_dec_ref(v_binderType_2853_);
lean_inc_ref(v_post_2840_);
lean_inc_ref(v_pre_2839_);
v___x_2857_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2839_, v_post_2840_, v_usedLetOnly_2841_, v_skipConstInApp_2842_, v_skipInstances_2843_, v___x_2856_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___f_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = lean_box(v_usedLetOnly_2841_);
v___x_2860_ = lean_box(v_skipConstInApp_2842_);
v___x_2861_ = lean_box(v_skipInstances_2843_);
v___f_2862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2862_, 0, v_fvars_2844_);
lean_closure_set(v___f_2862_, 1, v_pre_2839_);
lean_closure_set(v___f_2862_, 2, v_post_2840_);
lean_closure_set(v___f_2862_, 3, v___x_2859_);
lean_closure_set(v___f_2862_, 4, v___x_2860_);
lean_closure_set(v___f_2862_, 5, v___x_2861_);
lean_closure_set(v___f_2862_, 6, v_body_2854_);
v___x_2863_ = 0;
v___x_2864_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2852_, v_binderInfo_2855_, v_a_2858_, v___f_2862_, v___x_2863_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2864_;
}
else
{
lean_dec_ref(v_body_2854_);
lean_dec(v_binderName_2852_);
lean_dec_ref(v_fvars_2844_);
lean_dec_ref(v_post_2840_);
lean_dec_ref(v_pre_2839_);
return v___x_2857_;
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_expr_instantiate_rev(v_e_2845_, v_fvars_2844_);
lean_dec_ref(v_e_2845_);
lean_inc_ref(v_post_2840_);
lean_inc_ref(v_pre_2839_);
v___x_2866_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2839_, v_post_2840_, v_usedLetOnly_2841_, v_skipConstInApp_2842_, v_skipInstances_2843_, v___x_2865_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; uint8_t v___x_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = 0;
v___x_2869_ = 1;
v___x_2870_ = 1;
v___x_2871_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2844_, v_a_2867_, v___x_2868_, v_usedLetOnly_2841_, v___x_2868_, v___x_2869_, v___x_2870_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec_ref(v_fvars_2844_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2839_, v_post_2840_, v_usedLetOnly_2841_, v_skipConstInApp_2842_, v_skipInstances_2843_, v_a_2872_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
return v___x_2873_;
}
else
{
lean_dec_ref(v_post_2840_);
lean_dec_ref(v_pre_2839_);
return v___x_2871_;
}
}
else
{
lean_dec_ref(v_fvars_2844_);
lean_dec_ref(v_post_2840_);
lean_dec_ref(v_pre_2839_);
return v___x_2866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2874_, lean_object* v_pre_2875_, lean_object* v_post_2876_, uint8_t v_usedLetOnly_2877_, uint8_t v_skipConstInApp_2878_, uint8_t v_skipInstances_2879_, lean_object* v_body_2880_, lean_object* v_x_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_array_push(v_fvars_2874_, v_x_2881_);
v___x_2889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2875_, v_post_2876_, v_usedLetOnly_2877_, v_skipConstInApp_2878_, v_skipInstances_2879_, v___x_2888_, v_body_2880_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2890_, lean_object* v_pre_2891_, lean_object* v_post_2892_, lean_object* v_usedLetOnly_2893_, lean_object* v_skipConstInApp_2894_, lean_object* v_skipInstances_2895_, lean_object* v_body_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
uint8_t v_usedLetOnly_boxed_2904_; uint8_t v_skipConstInApp_boxed_2905_; uint8_t v_skipInstances_boxed_2906_; lean_object* v_res_2907_; 
v_usedLetOnly_boxed_2904_ = lean_unbox(v_usedLetOnly_2893_);
v_skipConstInApp_boxed_2905_ = lean_unbox(v_skipConstInApp_2894_);
v_skipInstances_boxed_2906_ = lean_unbox(v_skipInstances_2895_);
v_res_2907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2890_, v_pre_2891_, v_post_2892_, v_usedLetOnly_boxed_2904_, v_skipConstInApp_boxed_2905_, v_skipInstances_boxed_2906_, v_body_2896_, v_x_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2908_, lean_object* v_post_2909_, uint8_t v_usedLetOnly_2910_, uint8_t v_skipConstInApp_2911_, uint8_t v_skipInstances_2912_, lean_object* v_fvars_2913_, lean_object* v_e_2914_, lean_object* v_a_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
if (lean_obj_tag(v_e_2914_) == 8)
{
lean_object* v_declName_2921_; lean_object* v_type_2922_; lean_object* v_value_2923_; lean_object* v_body_2924_; uint8_t v_nondep_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_declName_2921_ = lean_ctor_get(v_e_2914_, 0);
lean_inc(v_declName_2921_);
v_type_2922_ = lean_ctor_get(v_e_2914_, 1);
lean_inc_ref(v_type_2922_);
v_value_2923_ = lean_ctor_get(v_e_2914_, 2);
lean_inc_ref(v_value_2923_);
v_body_2924_ = lean_ctor_get(v_e_2914_, 3);
lean_inc_ref(v_body_2924_);
v_nondep_2925_ = lean_ctor_get_uint8(v_e_2914_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2914_, 4);
v___x_2926_ = lean_expr_instantiate_rev(v_type_2922_, v_fvars_2913_);
lean_dec_ref(v_type_2922_);
lean_inc_ref(v_post_2909_);
lean_inc_ref(v_pre_2908_);
v___x_2927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2908_, v_post_2909_, v_usedLetOnly_2910_, v_skipConstInApp_2911_, v_skipInstances_2912_, v___x_2926_, v_a_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = lean_expr_instantiate_rev(v_value_2923_, v_fvars_2913_);
lean_dec_ref(v_value_2923_);
lean_inc_ref(v_post_2909_);
lean_inc_ref(v_pre_2908_);
v___x_2930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2908_, v_post_2909_, v_usedLetOnly_2910_, v_skipConstInApp_2911_, v_skipInstances_2912_, v___x_2929_, v_a_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___f_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = lean_box(v_usedLetOnly_2910_);
v___x_2933_ = lean_box(v_skipConstInApp_2911_);
v___x_2934_ = lean_box(v_skipInstances_2912_);
v___f_2935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2935_, 0, v_fvars_2913_);
lean_closure_set(v___f_2935_, 1, v_pre_2908_);
lean_closure_set(v___f_2935_, 2, v_post_2909_);
lean_closure_set(v___f_2935_, 3, v___x_2932_);
lean_closure_set(v___f_2935_, 4, v___x_2933_);
lean_closure_set(v___f_2935_, 5, v___x_2934_);
lean_closure_set(v___f_2935_, 6, v_body_2924_);
v___x_2936_ = 0;
v___x_2937_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2921_, v_a_2928_, v_a_2931_, v___f_2935_, v_nondep_2925_, v___x_2936_, v_a_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
return v___x_2937_;
}
else
{
lean_dec(v_a_2928_);
lean_dec_ref(v_body_2924_);
lean_dec(v_declName_2921_);
lean_dec_ref(v_fvars_2913_);
lean_dec_ref(v_post_2909_);
lean_dec_ref(v_pre_2908_);
return v___x_2930_;
}
}
else
{
lean_dec_ref(v_body_2924_);
lean_dec_ref(v_value_2923_);
lean_dec(v_declName_2921_);
lean_dec_ref(v_fvars_2913_);
lean_dec_ref(v_post_2909_);
lean_dec_ref(v_pre_2908_);
return v___x_2927_;
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_expr_instantiate_rev(v_e_2914_, v_fvars_2913_);
lean_dec_ref(v_e_2914_);
lean_inc_ref(v_post_2909_);
lean_inc_ref(v_pre_2908_);
v___x_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2908_, v_post_2909_, v_usedLetOnly_2910_, v_skipConstInApp_2911_, v_skipInstances_2912_, v___x_2938_, v_a_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; uint8_t v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = 0;
v___x_2942_ = 1;
v___x_2943_ = l_Lean_Meta_mkLetFVars(v_fvars_2913_, v_a_2940_, v_usedLetOnly_2910_, v___x_2941_, v___x_2942_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec_ref(v_fvars_2913_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2908_, v_post_2909_, v_usedLetOnly_2910_, v_skipConstInApp_2911_, v_skipInstances_2912_, v_a_2944_, v_a_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
return v___x_2945_;
}
else
{
lean_dec_ref(v_post_2909_);
lean_dec_ref(v_pre_2908_);
return v___x_2943_;
}
}
else
{
lean_dec_ref(v_fvars_2913_);
lean_dec_ref(v_post_2909_);
lean_dec_ref(v_pre_2908_);
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2946_, lean_object* v_post_2947_, uint8_t v_usedLetOnly_2948_, uint8_t v_skipConstInApp_2949_, uint8_t v_skipInstances_2950_, size_t v_sz_2951_, size_t v_i_2952_, lean_object* v_bs_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_usize_dec_lt(v_i_2952_, v_sz_2951_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec_ref(v_post_2947_);
lean_dec_ref(v_pre_2946_);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_bs_2953_);
return v___x_2961_;
}
else
{
lean_object* v_v_2962_; lean_object* v___x_2963_; 
v_v_2962_ = lean_array_uget_borrowed(v_bs_2953_, v_i_2952_);
lean_inc(v_v_2962_);
lean_inc_ref(v_post_2947_);
lean_inc_ref(v_pre_2946_);
v___x_2963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2946_, v_post_2947_, v_usedLetOnly_2948_, v_skipConstInApp_2949_, v_skipInstances_2950_, v_v_2962_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v_bs_x27_2966_; size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = lean_unsigned_to_nat(0u);
v_bs_x27_2966_ = lean_array_uset(v_bs_2953_, v_i_2952_, v___x_2965_);
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_add(v_i_2952_, v___x_2967_);
v___x_2969_ = lean_array_uset(v_bs_x27_2966_, v_i_2952_, v_a_2964_);
v_i_2952_ = v___x_2968_;
v_bs_2953_ = v___x_2969_;
goto _start;
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v_bs_2953_);
lean_dec_ref(v_post_2947_);
lean_dec_ref(v_pre_2946_);
v_a_2971_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2963_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2963_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2979_, lean_object* v_post_2980_, uint8_t v_usedLetOnly_2981_, uint8_t v_skipConstInApp_2982_, uint8_t v_skipInstances_2983_, lean_object* v___x_2984_, lean_object* v___y_2985_, lean_object* v_b_2986_, lean_object* v_a_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2979_, v_post_2980_, v_usedLetOnly_2981_, v_skipConstInApp_2982_, v_skipInstances_2983_, v___x_2984_, v___y_2985_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3003_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3003_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3003_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2998_ = lean_array_fset(v_b_2986_, v_a_2987_, v_a_2994_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2999_);
v___x_3001_ = v___x_2996_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec_ref(v_b_2986_);
v_a_3004_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2993_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2993_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3012_, lean_object* v_post_3013_, lean_object* v_usedLetOnly_3014_, lean_object* v_skipConstInApp_3015_, lean_object* v_skipInstances_3016_, lean_object* v___x_3017_, lean_object* v___y_3018_, lean_object* v_b_3019_, lean_object* v_a_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
uint8_t v_usedLetOnly_boxed_3026_; uint8_t v_skipConstInApp_boxed_3027_; uint8_t v_skipInstances_boxed_3028_; lean_object* v_res_3029_; 
v_usedLetOnly_boxed_3026_ = lean_unbox(v_usedLetOnly_3014_);
v_skipConstInApp_boxed_3027_ = lean_unbox(v_skipConstInApp_3015_);
v_skipInstances_boxed_3028_ = lean_unbox(v_skipInstances_3016_);
v_res_3029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3012_, v_post_3013_, v_usedLetOnly_boxed_3026_, v_skipConstInApp_boxed_3027_, v_skipInstances_boxed_3028_, v___x_3017_, v___y_3018_, v_b_3019_, v_a_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v_a_3020_);
lean_dec(v___y_3018_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3030_, lean_object* v___x_3031_, lean_object* v_pre_3032_, lean_object* v_post_3033_, uint8_t v_usedLetOnly_3034_, uint8_t v_skipConstInApp_3035_, uint8_t v_skipInstances_3036_, lean_object* v_a_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___y_3046_; uint8_t v___x_3069_; 
v___x_3069_ = lean_nat_dec_lt(v_a_3037_, v_upperBound_3030_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
lean_dec(v_a_3037_);
lean_dec_ref(v_post_3033_);
lean_dec_ref(v_pre_3032_);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_b_3038_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3071_ = lean_array_fget_borrowed(v_b_3038_, v_a_3037_);
v___x_3072_ = lean_array_get_size(v___x_3031_);
v___x_3073_ = lean_nat_dec_lt(v_a_3037_, v___x_3072_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___f_3077_; 
lean_inc(v___x_3071_);
v___x_3074_ = lean_box(v_usedLetOnly_3034_);
v___x_3075_ = lean_box(v_skipConstInApp_3035_);
v___x_3076_ = lean_box(v_skipInstances_3036_);
lean_inc(v_a_3037_);
lean_inc(v___y_3039_);
lean_inc_ref(v_post_3033_);
lean_inc_ref(v_pre_3032_);
v___f_3077_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3077_, 0, v_pre_3032_);
lean_closure_set(v___f_3077_, 1, v_post_3033_);
lean_closure_set(v___f_3077_, 2, v___x_3074_);
lean_closure_set(v___f_3077_, 3, v___x_3075_);
lean_closure_set(v___f_3077_, 4, v___x_3076_);
lean_closure_set(v___f_3077_, 5, v___x_3071_);
lean_closure_set(v___f_3077_, 6, v___y_3039_);
lean_closure_set(v___f_3077_, 7, v_b_3038_);
lean_closure_set(v___f_3077_, 8, v_a_3037_);
v___y_3046_ = v___f_3077_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3078_; uint8_t v_isInstance_3079_; 
v___x_3078_ = lean_array_fget_borrowed(v___x_3031_, v_a_3037_);
v_isInstance_3079_ = lean_ctor_get_uint8(v___x_3078_, sizeof(void*)*1 + 4);
if (v_isInstance_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; 
lean_inc(v___x_3071_);
v___x_3080_ = lean_box(v_usedLetOnly_3034_);
v___x_3081_ = lean_box(v_skipConstInApp_3035_);
v___x_3082_ = lean_box(v_skipInstances_3036_);
lean_inc(v_a_3037_);
lean_inc(v___y_3039_);
lean_inc_ref(v_post_3033_);
lean_inc_ref(v_pre_3032_);
v___f_3083_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3083_, 0, v_pre_3032_);
lean_closure_set(v___f_3083_, 1, v_post_3033_);
lean_closure_set(v___f_3083_, 2, v___x_3080_);
lean_closure_set(v___f_3083_, 3, v___x_3081_);
lean_closure_set(v___f_3083_, 4, v___x_3082_);
lean_closure_set(v___f_3083_, 5, v___x_3071_);
lean_closure_set(v___f_3083_, 6, v___y_3039_);
lean_closure_set(v___f_3083_, 7, v_b_3038_);
lean_closure_set(v___f_3083_, 8, v_a_3037_);
v___y_3046_ = v___f_3083_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3084_; lean_object* v___f_3085_; 
v___x_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_b_3038_);
v___f_3085_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3085_, 0, v___x_3084_);
v___y_3046_ = v___f_3085_;
goto v___jp_3045_;
}
}
}
v___jp_3045_:
{
lean_object* v___x_3047_; 
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc_ref(v___y_3040_);
v___x_3047_ = lean_apply_5(v___y_3046_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, lean_box(0));
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3060_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3060_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3060_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
if (lean_obj_tag(v_a_3048_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; 
lean_dec(v_a_3037_);
lean_dec_ref(v_post_3033_);
lean_dec_ref(v_pre_3032_);
v_a_3052_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v_a_3048_, 1);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_a_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_del_object(v___x_3050_);
v_a_3056_ = lean_ctor_get(v_a_3048_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v_a_3048_, 1);
v___x_3057_ = lean_unsigned_to_nat(1u);
v___x_3058_ = lean_nat_add(v_a_3037_, v___x_3057_);
lean_dec(v_a_3037_);
v_a_3037_ = v___x_3058_;
v_b_3038_ = v_a_3056_;
goto _start;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_3037_);
lean_dec_ref(v_post_3033_);
lean_dec_ref(v_pre_3032_);
v_a_3061_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3047_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3047_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3086_, lean_object* v_pre_3087_, lean_object* v_post_3088_, uint8_t v_usedLetOnly_3089_, uint8_t v_skipConstInApp_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_f_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; 
if (lean_obj_tag(v_x_3091_) == 5)
{
lean_object* v_fn_3149_; lean_object* v_arg_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_fn_3149_ = lean_ctor_get(v_x_3091_, 0);
lean_inc_ref(v_fn_3149_);
v_arg_3150_ = lean_ctor_get(v_x_3091_, 1);
lean_inc_ref(v_arg_3150_);
lean_dec_ref_known(v_x_3091_, 2);
v___x_3151_ = lean_array_set(v_x_3092_, v_x_3093_, v_arg_3150_);
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_nat_sub(v_x_3093_, v___x_3152_);
lean_dec(v_x_3093_);
v_x_3091_ = v_fn_3149_;
v_x_3092_ = v___x_3151_;
v_x_3093_ = v___x_3153_;
goto _start;
}
else
{
lean_dec(v_x_3093_);
if (v_skipConstInApp_3090_ == 0)
{
goto v___jp_3146_;
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = l_Lean_Expr_isConst(v_x_3091_);
if (v___x_3155_ == 0)
{
goto v___jp_3146_;
}
else
{
v_f_3101_ = v_x_3091_;
v___y_3102_ = v___y_3094_;
v___y_3103_ = v___y_3095_;
v___y_3104_ = v___y_3096_;
v___y_3105_ = v___y_3097_;
v___y_3106_ = v___y_3098_;
goto v___jp_3100_;
}
}
}
v___jp_3100_:
{
if (v_skipInstances_3086_ == 0)
{
size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v_sz_3107_ = lean_array_size(v_x_3092_);
v___x_3108_ = ((size_t)0ULL);
lean_inc_ref(v_post_3088_);
lean_inc_ref(v_pre_3087_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3087_, v_post_3088_, v_usedLetOnly_3089_, v_skipConstInApp_3090_, v_skipInstances_3086_, v_sz_3107_, v___x_3108_, v_x_3092_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = l_Lean_mkAppN(v_f_3101_, v_a_3110_);
lean_dec(v_a_3110_);
v___x_3112_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3087_, v_post_3088_, v_usedLetOnly_3089_, v_skipConstInApp_3090_, v_skipInstances_3086_, v___x_3111_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
return v___x_3112_;
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_f_3101_);
lean_dec_ref(v_post_3088_);
lean_dec_ref(v_pre_3087_);
v_a_3113_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3109_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3109_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_array_get_size(v_x_3092_);
lean_inc_ref(v_f_3101_);
v___x_3122_ = l_Lean_Meta_getFunInfoNArgs(v_f_3101_, v___x_3121_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_paramInfo_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v_paramInfo_3124_ = lean_ctor_get(v_a_3123_, 0);
lean_inc_ref(v_paramInfo_3124_);
lean_dec(v_a_3123_);
v___x_3125_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3088_);
lean_inc_ref(v_pre_3087_);
v___x_3126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3121_, v_paramInfo_3124_, v_pre_3087_, v_post_3088_, v_usedLetOnly_3089_, v_skipConstInApp_3090_, v_skipInstances_3086_, v___x_3125_, v_x_3092_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec_ref(v_paramInfo_3124_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = l_Lean_mkAppN(v_f_3101_, v_a_3127_);
lean_dec(v_a_3127_);
v___x_3129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3087_, v_post_3088_, v_usedLetOnly_3089_, v_skipConstInApp_3090_, v_skipInstances_3086_, v___x_3128_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
return v___x_3129_;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v_f_3101_);
lean_dec_ref(v_post_3088_);
lean_dec_ref(v_pre_3087_);
v_a_3130_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3126_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3126_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_f_3101_);
lean_dec_ref(v_x_3092_);
lean_dec_ref(v_post_3088_);
lean_dec_ref(v_pre_3087_);
v_a_3138_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3122_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3122_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
v___jp_3146_:
{
lean_object* v___x_3147_; 
lean_inc_ref(v_post_3088_);
lean_inc_ref(v_pre_3087_);
v___x_3147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3087_, v_post_3088_, v_usedLetOnly_3089_, v_skipConstInApp_3090_, v_skipInstances_3086_, v_x_3091_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v_f_3101_ = v_a_3148_;
v___y_3102_ = v___y_3094_;
v___y_3103_ = v___y_3095_;
v___y_3104_ = v___y_3096_;
v___y_3105_ = v___y_3097_;
v___y_3106_ = v___y_3098_;
goto v___jp_3100_;
}
else
{
lean_dec_ref(v_x_3092_);
lean_dec_ref(v_post_3088_);
lean_dec_ref(v_pre_3087_);
return v___x_3147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3156_, lean_object* v_pre_3157_, lean_object* v_e_3158_, lean_object* v_post_3159_, uint8_t v_usedLetOnly_3160_, uint8_t v_skipConstInApp_3161_, uint8_t v_skipInstances_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Core_checkSystem(v___x_3156_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref_known(v___x_3169_, 1);
lean_inc_ref(v_pre_3157_);
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
lean_inc_ref(v_e_3158_);
v___x_3170_ = lean_apply_6(v_pre_3157_, v_e_3158_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3219_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3219_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3219_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___y_3176_; 
switch(lean_obj_tag(v_a_3171_))
{
case 0:
{
lean_object* v_e_3211_; lean_object* v___x_3213_; 
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_e_3158_);
lean_dec_ref(v_pre_3157_);
v_e_3211_ = lean_ctor_get(v_a_3171_, 0);
lean_inc_ref(v_e_3211_);
lean_dec_ref_known(v_a_3171_, 1);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_e_3211_);
v___x_3213_ = v___x_3173_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_e_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
case 1:
{
lean_object* v_e_3215_; lean_object* v___x_3216_; 
lean_del_object(v___x_3173_);
lean_dec_ref(v_e_3158_);
v_e_3215_ = lean_ctor_get(v_a_3171_, 0);
lean_inc_ref(v_e_3215_);
lean_dec_ref_known(v_a_3171_, 1);
v___x_3216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_e_3215_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3216_;
}
default: 
{
lean_object* v_e_x3f_3217_; 
lean_del_object(v___x_3173_);
v_e_x3f_3217_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_e_x3f_3217_);
lean_dec_ref_known(v_a_3171_, 1);
if (lean_obj_tag(v_e_x3f_3217_) == 0)
{
v___y_3176_ = v_e_3158_;
goto v___jp_3175_;
}
else
{
lean_object* v_val_3218_; 
lean_dec_ref(v_e_3158_);
v_val_3218_ = lean_ctor_get(v_e_x3f_3217_, 0);
lean_inc(v_val_3218_);
lean_dec_ref_known(v_e_x3f_3217_, 1);
v___y_3176_ = v_val_3218_;
goto v___jp_3175_;
}
}
}
v___jp_3175_:
{
switch(lean_obj_tag(v___y_3176_))
{
case 7:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3177_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3178_;
}
case 6:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3179_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3180_;
}
case 8:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3181_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3182_;
}
case 5:
{
lean_object* v_dummy_3183_; lean_object* v_nargs_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_dummy_3183_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3184_ = l_Lean_Expr_getAppNumArgs(v___y_3176_);
lean_inc(v_nargs_3184_);
v___x_3185_ = lean_mk_array(v_nargs_3184_, v_dummy_3183_);
v___x_3186_ = lean_unsigned_to_nat(1u);
v___x_3187_ = lean_nat_sub(v_nargs_3184_, v___x_3186_);
lean_dec(v_nargs_3184_);
v___x_3188_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3162_, v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v___y_3176_, v___x_3185_, v___x_3187_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3188_;
}
case 10:
{
lean_object* v_data_3189_; lean_object* v_expr_3190_; lean_object* v___x_3191_; 
v_data_3189_ = lean_ctor_get(v___y_3176_, 0);
v_expr_3190_ = lean_ctor_get(v___y_3176_, 1);
lean_inc_ref(v_expr_3190_);
lean_inc_ref(v_post_3159_);
lean_inc_ref(v_pre_3157_);
v___x_3191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_expr_3190_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; size_t v___x_3193_; size_t v___x_3194_; uint8_t v___x_3195_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = lean_ptr_addr(v_expr_3190_);
v___x_3194_ = lean_ptr_addr(v_a_3192_);
v___x_3195_ = lean_usize_dec_eq(v___x_3193_, v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_inc(v_data_3189_);
lean_dec_ref_known(v___y_3176_, 2);
v___x_3196_ = l_Lean_Expr_mdata___override(v_data_3189_, v_a_3192_);
v___x_3197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3196_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; 
lean_dec(v_a_3192_);
v___x_3198_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3198_;
}
}
else
{
lean_dec_ref_known(v___y_3176_, 2);
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_pre_3157_);
return v___x_3191_;
}
}
case 11:
{
lean_object* v_typeName_3199_; lean_object* v_idx_3200_; lean_object* v_struct_3201_; lean_object* v___x_3202_; 
v_typeName_3199_ = lean_ctor_get(v___y_3176_, 0);
v_idx_3200_ = lean_ctor_get(v___y_3176_, 1);
v_struct_3201_ = lean_ctor_get(v___y_3176_, 2);
lean_inc_ref(v_struct_3201_);
lean_inc_ref(v_post_3159_);
lean_inc_ref(v_pre_3157_);
v___x_3202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_struct_3201_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; size_t v___x_3204_; size_t v___x_3205_; uint8_t v___x_3206_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v___x_3204_ = lean_ptr_addr(v_struct_3201_);
v___x_3205_ = lean_ptr_addr(v_a_3203_);
v___x_3206_ = lean_usize_dec_eq(v___x_3204_, v___x_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_inc(v_idx_3200_);
lean_inc(v_typeName_3199_);
lean_dec_ref_known(v___y_3176_, 3);
v___x_3207_ = l_Lean_Expr_proj___override(v_typeName_3199_, v_idx_3200_, v_a_3203_);
v___x_3208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3207_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3208_;
}
else
{
lean_object* v___x_3209_; 
lean_dec(v_a_3203_);
v___x_3209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3209_;
}
}
else
{
lean_dec_ref_known(v___y_3176_, 3);
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_pre_3157_);
return v___x_3202_;
}
}
default: 
{
lean_object* v___x_3210_; 
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3157_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___y_3176_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3210_;
}
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_e_3158_);
lean_dec_ref(v_pre_3157_);
v_a_3220_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3170_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3170_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_e_3158_);
lean_dec_ref(v_pre_3157_);
v_a_3228_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3169_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3169_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3236_, lean_object* v_pre_3237_, lean_object* v_e_3238_, lean_object* v_post_3239_, lean_object* v_usedLetOnly_3240_, lean_object* v_skipConstInApp_3241_, lean_object* v_skipInstances_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_usedLetOnly_boxed_3249_; uint8_t v_skipConstInApp_boxed_3250_; uint8_t v_skipInstances_boxed_3251_; lean_object* v_res_3252_; 
v_usedLetOnly_boxed_3249_ = lean_unbox(v_usedLetOnly_3240_);
v_skipConstInApp_boxed_3250_ = lean_unbox(v_skipConstInApp_3241_);
v_skipInstances_boxed_3251_ = lean_unbox(v_skipInstances_3242_);
v_res_3252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3236_, v_pre_3237_, v_e_3238_, v_post_3239_, v_usedLetOnly_boxed_3249_, v_skipConstInApp_boxed_3250_, v_skipInstances_boxed_3251_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3253_, lean_object* v_post_3254_, uint8_t v_usedLetOnly_3255_, uint8_t v_skipConstInApp_3256_, uint8_t v_skipInstances_3257_, lean_object* v_e_3258_, lean_object* v_a_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_inc(v_a_3259_);
v___x_3265_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3265_, 0, lean_box(0));
lean_closure_set(v___x_3265_, 1, lean_box(0));
lean_closure_set(v___x_3265_, 2, v_a_3259_);
v___x_3266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3265_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3301_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3301_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3301_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3267_, v_e_3258_);
lean_dec(v_a_3267_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___f_3276_; lean_object* v___x_3277_; 
lean_del_object(v___x_3269_);
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3273_ = lean_box(v_usedLetOnly_3255_);
v___x_3274_ = lean_box(v_skipConstInApp_3256_);
v___x_3275_ = lean_box(v_skipInstances_3257_);
lean_inc_ref(v_e_3258_);
v___f_3276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3276_, 0, v___x_3272_);
lean_closure_set(v___f_3276_, 1, v_pre_3253_);
lean_closure_set(v___f_3276_, 2, v_e_3258_);
lean_closure_set(v___f_3276_, 3, v_post_3254_);
lean_closure_set(v___f_3276_, 4, v___x_3273_);
lean_closure_set(v___f_3276_, 5, v___x_3274_);
lean_closure_set(v___f_3276_, 6, v___x_3275_);
v___x_3277_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3276_, v_a_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_n(v_a_3278_, 2);
lean_dec_ref_known(v___x_3277_, 1);
lean_inc(v_a_3259_);
v___f_3279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3279_, 0, v_a_3259_);
lean_closure_set(v___f_3279_, 1, v_e_3258_);
lean_closure_set(v___f_3279_, 2, v_a_3278_);
v___x_3280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3279_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3288_);
v___x_3282_ = v___x_3280_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v___x_3280_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v_a_3278_);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3278_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_a_3278_);
v_a_3289_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3280_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3280_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_dec_ref(v_e_3258_);
return v___x_3277_;
}
}
else
{
lean_object* v_val_3297_; lean_object* v___x_3299_; 
lean_dec_ref(v_e_3258_);
lean_dec_ref(v_post_3254_);
lean_dec_ref(v_pre_3253_);
v_val_3297_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v___x_3271_, 1);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v_val_3297_);
v___x_3299_ = v___x_3269_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_val_3297_);
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
lean_dec_ref(v_e_3258_);
lean_dec_ref(v_post_3254_);
lean_dec_ref(v_pre_3253_);
v_a_3302_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3266_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3266_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3310_, lean_object* v_pre_3311_, lean_object* v_post_3312_, lean_object* v_usedLetOnly_3313_, lean_object* v_skipConstInApp_3314_, lean_object* v_skipInstances_3315_, lean_object* v_body_3316_, lean_object* v_x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v_usedLetOnly_boxed_3324_; uint8_t v_skipConstInApp_boxed_3325_; uint8_t v_skipInstances_boxed_3326_; lean_object* v_res_3327_; 
v_usedLetOnly_boxed_3324_ = lean_unbox(v_usedLetOnly_3313_);
v_skipConstInApp_boxed_3325_ = lean_unbox(v_skipConstInApp_3314_);
v_skipInstances_boxed_3326_ = lean_unbox(v_skipInstances_3315_);
v_res_3327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3310_, v_pre_3311_, v_post_3312_, v_usedLetOnly_boxed_3324_, v_skipConstInApp_boxed_3325_, v_skipInstances_boxed_3326_, v_body_3316_, v_x_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3328_, lean_object* v_post_3329_, uint8_t v_usedLetOnly_3330_, uint8_t v_skipConstInApp_3331_, uint8_t v_skipInstances_3332_, lean_object* v_fvars_3333_, lean_object* v_e_3334_, lean_object* v_a_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
if (lean_obj_tag(v_e_3334_) == 7)
{
lean_object* v_binderName_3341_; lean_object* v_binderType_3342_; lean_object* v_body_3343_; uint8_t v_binderInfo_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_binderName_3341_ = lean_ctor_get(v_e_3334_, 0);
lean_inc(v_binderName_3341_);
v_binderType_3342_ = lean_ctor_get(v_e_3334_, 1);
lean_inc_ref(v_binderType_3342_);
v_body_3343_ = lean_ctor_get(v_e_3334_, 2);
lean_inc_ref(v_body_3343_);
v_binderInfo_3344_ = lean_ctor_get_uint8(v_e_3334_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3334_, 3);
v___x_3345_ = lean_expr_instantiate_rev(v_binderType_3342_, v_fvars_3333_);
lean_dec_ref(v_binderType_3342_);
lean_inc_ref(v_post_3329_);
lean_inc_ref(v_pre_3328_);
v___x_3346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3328_, v_post_3329_, v_usedLetOnly_3330_, v_skipConstInApp_3331_, v_skipInstances_3332_, v___x_3345_, v_a_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___f_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_box(v_usedLetOnly_3330_);
v___x_3349_ = lean_box(v_skipConstInApp_3331_);
v___x_3350_ = lean_box(v_skipInstances_3332_);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3351_, 0, v_fvars_3333_);
lean_closure_set(v___f_3351_, 1, v_pre_3328_);
lean_closure_set(v___f_3351_, 2, v_post_3329_);
lean_closure_set(v___f_3351_, 3, v___x_3348_);
lean_closure_set(v___f_3351_, 4, v___x_3349_);
lean_closure_set(v___f_3351_, 5, v___x_3350_);
lean_closure_set(v___f_3351_, 6, v_body_3343_);
v___x_3352_ = 0;
v___x_3353_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3341_, v_binderInfo_3344_, v_a_3347_, v___f_3351_, v___x_3352_, v_a_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3353_;
}
else
{
lean_dec_ref(v_body_3343_);
lean_dec(v_binderName_3341_);
lean_dec_ref(v_fvars_3333_);
lean_dec_ref(v_post_3329_);
lean_dec_ref(v_pre_3328_);
return v___x_3346_;
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3354_ = lean_expr_instantiate_rev(v_e_3334_, v_fvars_3333_);
lean_dec_ref(v_e_3334_);
lean_inc_ref(v_post_3329_);
lean_inc_ref(v_pre_3328_);
v___x_3355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3328_, v_post_3329_, v_usedLetOnly_3330_, v_skipConstInApp_3331_, v_skipInstances_3332_, v___x_3354_, v_a_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; uint8_t v___x_3357_; uint8_t v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref_known(v___x_3355_, 1);
v___x_3357_ = 0;
v___x_3358_ = 1;
v___x_3359_ = 1;
v___x_3360_ = l_Lean_Meta_mkForallFVars(v_fvars_3333_, v_a_3356_, v___x_3357_, v_usedLetOnly_3330_, v___x_3358_, v___x_3359_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec_ref(v_fvars_3333_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3328_, v_post_3329_, v_usedLetOnly_3330_, v_skipConstInApp_3331_, v_skipInstances_3332_, v_a_3361_, v_a_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3362_;
}
else
{
lean_dec_ref(v_post_3329_);
lean_dec_ref(v_pre_3328_);
return v___x_3360_;
}
}
else
{
lean_dec_ref(v_fvars_3333_);
lean_dec_ref(v_post_3329_);
lean_dec_ref(v_pre_3328_);
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3363_, lean_object* v_pre_3364_, lean_object* v_post_3365_, uint8_t v_usedLetOnly_3366_, uint8_t v_skipConstInApp_3367_, uint8_t v_skipInstances_3368_, lean_object* v_body_3369_, lean_object* v_x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_array_push(v_fvars_3363_, v_x_3370_);
v___x_3378_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3364_, v_post_3365_, v_usedLetOnly_3366_, v_skipConstInApp_3367_, v_skipInstances_3368_, v___x_3377_, v_body_3369_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3379_, lean_object* v_post_3380_, lean_object* v_usedLetOnly_3381_, lean_object* v_skipConstInApp_3382_, lean_object* v_skipInstances_3383_, lean_object* v_e_3384_, lean_object* v_a_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
uint8_t v_usedLetOnly_boxed_3391_; uint8_t v_skipConstInApp_boxed_3392_; uint8_t v_skipInstances_boxed_3393_; lean_object* v_res_3394_; 
v_usedLetOnly_boxed_3391_ = lean_unbox(v_usedLetOnly_3381_);
v_skipConstInApp_boxed_3392_ = lean_unbox(v_skipConstInApp_3382_);
v_skipInstances_boxed_3393_ = lean_unbox(v_skipInstances_3383_);
v_res_3394_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3379_, v_post_3380_, v_usedLetOnly_boxed_3391_, v_skipConstInApp_boxed_3392_, v_skipInstances_boxed_3393_, v_e_3384_, v_a_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v_a_3385_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3395_, lean_object* v_post_3396_, lean_object* v_usedLetOnly_3397_, lean_object* v_skipConstInApp_3398_, lean_object* v_skipInstances_3399_, lean_object* v_sz_3400_, lean_object* v_i_3401_, lean_object* v_bs_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
uint8_t v_usedLetOnly_boxed_3409_; uint8_t v_skipConstInApp_boxed_3410_; uint8_t v_skipInstances_boxed_3411_; size_t v_sz_boxed_3412_; size_t v_i_boxed_3413_; lean_object* v_res_3414_; 
v_usedLetOnly_boxed_3409_ = lean_unbox(v_usedLetOnly_3397_);
v_skipConstInApp_boxed_3410_ = lean_unbox(v_skipConstInApp_3398_);
v_skipInstances_boxed_3411_ = lean_unbox(v_skipInstances_3399_);
v_sz_boxed_3412_ = lean_unbox_usize(v_sz_3400_);
lean_dec(v_sz_3400_);
v_i_boxed_3413_ = lean_unbox_usize(v_i_3401_);
lean_dec(v_i_3401_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3395_, v_post_3396_, v_usedLetOnly_boxed_3409_, v_skipConstInApp_boxed_3410_, v_skipInstances_boxed_3411_, v_sz_boxed_3412_, v_i_boxed_3413_, v_bs_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3415_, lean_object* v_post_3416_, lean_object* v_usedLetOnly_3417_, lean_object* v_skipConstInApp_3418_, lean_object* v_skipInstances_3419_, lean_object* v_e_3420_, lean_object* v_a_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
uint8_t v_usedLetOnly_boxed_3427_; uint8_t v_skipConstInApp_boxed_3428_; uint8_t v_skipInstances_boxed_3429_; lean_object* v_res_3430_; 
v_usedLetOnly_boxed_3427_ = lean_unbox(v_usedLetOnly_3417_);
v_skipConstInApp_boxed_3428_ = lean_unbox(v_skipConstInApp_3418_);
v_skipInstances_boxed_3429_ = lean_unbox(v_skipInstances_3419_);
v_res_3430_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3415_, v_post_3416_, v_usedLetOnly_boxed_3427_, v_skipConstInApp_boxed_3428_, v_skipInstances_boxed_3429_, v_e_3420_, v_a_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v_a_3421_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3431_, lean_object* v_post_3432_, lean_object* v_usedLetOnly_3433_, lean_object* v_skipConstInApp_3434_, lean_object* v_skipInstances_3435_, lean_object* v_fvars_3436_, lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v_usedLetOnly_boxed_3444_; uint8_t v_skipConstInApp_boxed_3445_; uint8_t v_skipInstances_boxed_3446_; lean_object* v_res_3447_; 
v_usedLetOnly_boxed_3444_ = lean_unbox(v_usedLetOnly_3433_);
v_skipConstInApp_boxed_3445_ = lean_unbox(v_skipConstInApp_3434_);
v_skipInstances_boxed_3446_ = lean_unbox(v_skipInstances_3435_);
v_res_3447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3431_, v_post_3432_, v_usedLetOnly_boxed_3444_, v_skipConstInApp_boxed_3445_, v_skipInstances_boxed_3446_, v_fvars_3436_, v_e_3437_, v_a_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v_a_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3448_, lean_object* v_post_3449_, lean_object* v_usedLetOnly_3450_, lean_object* v_skipConstInApp_3451_, lean_object* v_skipInstances_3452_, lean_object* v_fvars_3453_, lean_object* v_e_3454_, lean_object* v_a_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_usedLetOnly_boxed_3461_; uint8_t v_skipConstInApp_boxed_3462_; uint8_t v_skipInstances_boxed_3463_; lean_object* v_res_3464_; 
v_usedLetOnly_boxed_3461_ = lean_unbox(v_usedLetOnly_3450_);
v_skipConstInApp_boxed_3462_ = lean_unbox(v_skipConstInApp_3451_);
v_skipInstances_boxed_3463_ = lean_unbox(v_skipInstances_3452_);
v_res_3464_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3448_, v_post_3449_, v_usedLetOnly_boxed_3461_, v_skipConstInApp_boxed_3462_, v_skipInstances_boxed_3463_, v_fvars_3453_, v_e_3454_, v_a_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v_a_3455_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3465_, lean_object* v_post_3466_, lean_object* v_usedLetOnly_3467_, lean_object* v_skipConstInApp_3468_, lean_object* v_skipInstances_3469_, lean_object* v_fvars_3470_, lean_object* v_e_3471_, lean_object* v_a_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v_usedLetOnly_boxed_3478_; uint8_t v_skipConstInApp_boxed_3479_; uint8_t v_skipInstances_boxed_3480_; lean_object* v_res_3481_; 
v_usedLetOnly_boxed_3478_ = lean_unbox(v_usedLetOnly_3467_);
v_skipConstInApp_boxed_3479_ = lean_unbox(v_skipConstInApp_3468_);
v_skipInstances_boxed_3480_ = lean_unbox(v_skipInstances_3469_);
v_res_3481_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3465_, v_post_3466_, v_usedLetOnly_boxed_3478_, v_skipConstInApp_boxed_3479_, v_skipInstances_boxed_3480_, v_fvars_3470_, v_e_3471_, v_a_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v_a_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3482_, lean_object* v___x_3483_, lean_object* v_pre_3484_, lean_object* v_post_3485_, lean_object* v_usedLetOnly_3486_, lean_object* v_skipConstInApp_3487_, lean_object* v_skipInstances_3488_, lean_object* v_a_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v_usedLetOnly_boxed_3497_; uint8_t v_skipConstInApp_boxed_3498_; uint8_t v_skipInstances_boxed_3499_; lean_object* v_res_3500_; 
v_usedLetOnly_boxed_3497_ = lean_unbox(v_usedLetOnly_3486_);
v_skipConstInApp_boxed_3498_ = lean_unbox(v_skipConstInApp_3487_);
v_skipInstances_boxed_3499_ = lean_unbox(v_skipInstances_3488_);
v_res_3500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3482_, v___x_3483_, v_pre_3484_, v_post_3485_, v_usedLetOnly_boxed_3497_, v_skipConstInApp_boxed_3498_, v_skipInstances_boxed_3499_, v_a_3489_, v_b_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___x_3483_);
lean_dec(v_upperBound_3482_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3501_, lean_object* v_pre_3502_, lean_object* v_post_3503_, lean_object* v_usedLetOnly_3504_, lean_object* v_skipConstInApp_3505_, lean_object* v_x_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v_skipInstances_boxed_3515_; uint8_t v_usedLetOnly_boxed_3516_; uint8_t v_skipConstInApp_boxed_3517_; lean_object* v_res_3518_; 
v_skipInstances_boxed_3515_ = lean_unbox(v_skipInstances_3501_);
v_usedLetOnly_boxed_3516_ = lean_unbox(v_usedLetOnly_3504_);
v_skipConstInApp_boxed_3517_ = lean_unbox(v_skipConstInApp_3505_);
v_res_3518_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3515_, v_pre_3502_, v_post_3503_, v_usedLetOnly_boxed_3516_, v_skipConstInApp_boxed_3517_, v_x_3506_, v_x_3507_, v_x_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = lean_box(0);
v___x_3520_ = lean_unsigned_to_nat(16u);
v___x_3521_ = lean_mk_array(v___x_3520_, v___x_3519_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3523_ = lean_unsigned_to_nat(0u);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___x_3522_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3526_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3526_, 0, lean_box(0));
lean_closure_set(v___x_3526_, 1, lean_box(0));
lean_closure_set(v___x_3526_, 2, v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3527_, lean_object* v_pre_3528_, lean_object* v_post_3529_, uint8_t v_usedLetOnly_3530_, uint8_t v_skipConstInApp_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v_a_3539_; uint8_t v___x_3540_; lean_object* v___x_3541_; 
v___x_3537_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3538_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3537_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = 0;
v___x_3541_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3528_, v_post_3529_, v_usedLetOnly_3530_, v_skipConstInApp_3531_, v___x_3540_, v_input_3527_, v_a_3539_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3543_, 0, lean_box(0));
lean_closure_set(v___x_3543_, 1, lean_box(0));
lean_closure_set(v___x_3543_, 2, v_a_3539_);
v___x_3544_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3543_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v___x_3544_, 0);
lean_dec(v_unused_3552_);
v___x_3546_ = v___x_3544_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_dec(v___x_3544_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v_a_3542_);
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3542_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
else
{
lean_dec(v_a_3539_);
return v___x_3541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3553_, lean_object* v_pre_3554_, lean_object* v_post_3555_, lean_object* v_usedLetOnly_3556_, lean_object* v_skipConstInApp_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_usedLetOnly_boxed_3563_; uint8_t v_skipConstInApp_boxed_3564_; lean_object* v_res_3565_; 
v_usedLetOnly_boxed_3563_ = lean_unbox(v_usedLetOnly_3556_);
v_skipConstInApp_boxed_3564_ = lean_unbox(v_skipConstInApp_3557_);
v_res_3565_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3553_, v_pre_3554_, v_post_3555_, v_usedLetOnly_boxed_3563_, v_skipConstInApp_boxed_3564_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3567_, lean_object* v_p_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v_a_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3574_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3567_, v_a_3570_);
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v___f_3576_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3577_, 0, v_p_3568_);
v___x_3578_ = 0;
v___x_3579_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3575_, v___f_3576_, v___f_3577_, v___x_3578_, v___x_3578_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3580_, lean_object* v_p_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_etaStructReduce(v_e_3580_, v_p_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3588_, lean_object* v___x_3589_, lean_object* v_pre_3590_, lean_object* v_post_3591_, uint8_t v_usedLetOnly_3592_, uint8_t v_skipConstInApp_3593_, uint8_t v_skipInstances_3594_, lean_object* v___x_3595_, lean_object* v_inst_3596_, lean_object* v_R_3597_, lean_object* v_a_3598_, lean_object* v_b_3599_, lean_object* v_c_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3588_, v___x_3589_, v_pre_3590_, v_post_3591_, v_usedLetOnly_3592_, v_skipConstInApp_3593_, v_skipInstances_3594_, v_a_3598_, v_b_3599_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3608_ = _args[0];
lean_object* v___x_3609_ = _args[1];
lean_object* v_pre_3610_ = _args[2];
lean_object* v_post_3611_ = _args[3];
lean_object* v_usedLetOnly_3612_ = _args[4];
lean_object* v_skipConstInApp_3613_ = _args[5];
lean_object* v_skipInstances_3614_ = _args[6];
lean_object* v___x_3615_ = _args[7];
lean_object* v_inst_3616_ = _args[8];
lean_object* v_R_3617_ = _args[9];
lean_object* v_a_3618_ = _args[10];
lean_object* v_b_3619_ = _args[11];
lean_object* v_c_3620_ = _args[12];
lean_object* v___y_3621_ = _args[13];
lean_object* v___y_3622_ = _args[14];
lean_object* v___y_3623_ = _args[15];
lean_object* v___y_3624_ = _args[16];
lean_object* v___y_3625_ = _args[17];
lean_object* v___y_3626_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3627_; uint8_t v_skipConstInApp_boxed_3628_; uint8_t v_skipInstances_boxed_3629_; lean_object* v_res_3630_; 
v_usedLetOnly_boxed_3627_ = lean_unbox(v_usedLetOnly_3612_);
v_skipConstInApp_boxed_3628_ = lean_unbox(v_skipConstInApp_3613_);
v_skipInstances_boxed_3629_ = lean_unbox(v_skipInstances_3614_);
v_res_3630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3608_, v___x_3609_, v_pre_3610_, v_post_3611_, v_usedLetOnly_boxed_3627_, v_skipConstInApp_boxed_3628_, v_skipInstances_boxed_3629_, v___x_3615_, v_inst_3616_, v_R_3617_, v_a_3618_, v_b_3619_, v_c_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec(v___x_3615_);
lean_dec_ref(v___x_3609_);
lean_dec(v_upperBound_3608_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3631_, lean_object* v_m_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3632_, v_a_3633_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3635_, lean_object* v_m_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3635_, v_m_3636_, v_a_3637_);
lean_dec_ref(v_a_3637_);
lean_dec_ref(v_m_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3639_, lean_object* v_name_3640_, uint8_t v_bi_3641_, lean_object* v_type_3642_, lean_object* v_k_3643_, uint8_t v_kind_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3640_, v_bi_3641_, v_type_3642_, v_k_3643_, v_kind_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_name_3653_, lean_object* v_bi_3654_, lean_object* v_type_3655_, lean_object* v_k_3656_, lean_object* v_kind_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
uint8_t v_bi_boxed_3664_; uint8_t v_kind_boxed_3665_; lean_object* v_res_3666_; 
v_bi_boxed_3664_ = lean_unbox(v_bi_3654_);
v_kind_boxed_3665_ = lean_unbox(v_kind_3657_);
v_res_3666_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3652_, v_name_3653_, v_bi_boxed_3664_, v_type_3655_, v_k_3656_, v_kind_boxed_3665_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3667_, lean_object* v_name_3668_, lean_object* v_type_3669_, lean_object* v_val_3670_, lean_object* v_k_3671_, uint8_t v_nondep_3672_, uint8_t v_kind_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3668_, v_type_3669_, v_val_3670_, v_k_3671_, v_nondep_3672_, v_kind_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3681_, lean_object* v_name_3682_, lean_object* v_type_3683_, lean_object* v_val_3684_, lean_object* v_k_3685_, lean_object* v_nondep_3686_, lean_object* v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
uint8_t v_nondep_boxed_3694_; uint8_t v_kind_boxed_3695_; lean_object* v_res_3696_; 
v_nondep_boxed_3694_ = lean_unbox(v_nondep_3686_);
v_kind_boxed_3695_ = lean_unbox(v_kind_3687_);
v_res_3696_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3681_, v_name_3682_, v_type_3683_, v_val_3684_, v_k_3685_, v_nondep_boxed_3694_, v_kind_boxed_3695_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3697_, lean_object* v_ref_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3698_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3705_, lean_object* v_ref_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3705_, v_ref_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3713_, lean_object* v_x_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3722_, lean_object* v_x_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3722_, v_x_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3731_, lean_object* v_m_3732_, lean_object* v_a_3733_, lean_object* v_b_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3732_, v_a_3733_, v_b_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3736_, lean_object* v_a_3737_, lean_object* v_x_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3737_, v_x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3740_, lean_object* v_a_3741_, lean_object* v_x_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3740_, v_a_3741_, v_x_3742_);
lean_dec(v_x_3742_);
lean_dec_ref(v_a_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3744_, lean_object* v_a_3745_, lean_object* v_x_3746_){
_start:
{
uint8_t v___x_3747_; 
v___x_3747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3745_, v_x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3748_, lean_object* v_a_3749_, lean_object* v_x_3750_){
_start:
{
uint8_t v_res_3751_; lean_object* v_r_3752_; 
v_res_3751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3748_, v_a_3749_, v_x_3750_);
lean_dec(v_x_3750_);
lean_dec_ref(v_a_3749_);
v_r_3752_ = lean_box(v_res_3751_);
return v_r_3752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3753_, lean_object* v_data_3754_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3756_, lean_object* v_a_3757_, lean_object* v_b_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3757_, v_b_3758_, v_x_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3761_, lean_object* v_i_3762_, lean_object* v_source_3763_, lean_object* v_target_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3762_, v_source_3763_, v_target_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3767_, v_x_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3770_, lean_object* v_inst_3771_, lean_object* v_toBind_3772_, lean_object* v___f_3773_, lean_object* v_____do__lift_3774_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3775_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3775_, 0, v_____do__lift_3774_);
lean_closure_set(v___x_3775_, 1, v_binderType_3770_);
v___x_3776_ = lean_apply_2(v_inst_3771_, lean_box(0), v___x_3775_);
v___x_3777_ = lean_apply_4(v_toBind_3772_, lean_box(0), lean_box(0), v___x_3776_, v___f_3773_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3778_, lean_object* v_usedFields_3779_, lean_object* v_binderName_3780_, lean_object* v_body_3781_, lean_object* v_val_3782_, lean_object* v_inst_3783_, lean_object* v_inst_3784_, lean_object* v_fieldVal_x3f_3785_, lean_object* v_____do__lift_3786_){
_start:
{
uint8_t v_____do__lift_289__boxed_3787_; lean_object* v_res_3788_; 
v_____do__lift_289__boxed_3787_ = lean_unbox(v_____do__lift_3786_);
v_res_3788_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3778_, v_usedFields_3779_, v_binderName_3780_, v_body_3781_, v_val_3782_, v_inst_3783_, v_inst_3784_, v_fieldVal_x3f_3785_, v_____do__lift_289__boxed_3787_);
lean_dec_ref(v_val_3782_);
lean_dec_ref(v_body_3781_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3789_, lean_object* v_usedFields_3790_, lean_object* v_binderName_3791_, lean_object* v_body_3792_, lean_object* v_inst_3793_, lean_object* v_inst_3794_, lean_object* v_fieldVal_x3f_3795_, lean_object* v_binderType_3796_, lean_object* v_toBind_3797_, lean_object* v_____x_3798_){
_start:
{
if (lean_obj_tag(v_____x_3798_) == 1)
{
lean_object* v_val_3799_; lean_object* v___f_3800_; lean_object* v___f_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_val_3799_ = lean_ctor_get(v_____x_3798_, 0);
lean_inc_n(v_val_3799_, 2);
lean_dec_ref_known(v_____x_3798_, 1);
lean_inc_n(v_inst_3794_, 2);
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3800_, 0, v_toPure_3789_);
lean_closure_set(v___f_3800_, 1, v_usedFields_3790_);
lean_closure_set(v___f_3800_, 2, v_binderName_3791_);
lean_closure_set(v___f_3800_, 3, v_body_3792_);
lean_closure_set(v___f_3800_, 4, v_val_3799_);
lean_closure_set(v___f_3800_, 5, v_inst_3793_);
lean_closure_set(v___f_3800_, 6, v_inst_3794_);
lean_closure_set(v___f_3800_, 7, v_fieldVal_x3f_3795_);
lean_inc(v_toBind_3797_);
v___f_3801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3801_, 0, v_binderType_3796_);
lean_closure_set(v___f_3801_, 1, v_inst_3794_);
lean_closure_set(v___f_3801_, 2, v_toBind_3797_);
lean_closure_set(v___f_3801_, 3, v___f_3800_);
v___x_3802_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3802_, 0, v_val_3799_);
v___x_3803_ = lean_apply_2(v_inst_3794_, lean_box(0), v___x_3802_);
v___x_3804_ = lean_apply_4(v_toBind_3797_, lean_box(0), lean_box(0), v___x_3803_, v___f_3801_);
return v___x_3804_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec(v_____x_3798_);
lean_dec(v_toBind_3797_);
lean_dec_ref(v_binderType_3796_);
lean_dec(v_fieldVal_x3f_3795_);
lean_dec(v_inst_3794_);
lean_dec_ref(v_inst_3793_);
lean_dec_ref(v_body_3792_);
lean_dec(v_binderName_3791_);
lean_dec(v_usedFields_3790_);
v___x_3805_ = lean_box(0);
v___x_3806_ = lean_apply_2(v_toPure_3789_, lean_box(0), v___x_3805_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_fieldVal_x3f_3812_, lean_object* v_usedFields_3813_, lean_object* v_e_3814_){
_start:
{
lean_object* v_toApplicative_3815_; lean_object* v_toBind_3816_; lean_object* v_toPure_3817_; 
v_toApplicative_3815_ = lean_ctor_get(v_inst_3810_, 0);
v_toBind_3816_ = lean_ctor_get(v_inst_3810_, 1);
v_toPure_3817_ = lean_ctor_get(v_toApplicative_3815_, 1);
lean_inc(v_toPure_3817_);
if (lean_obj_tag(v_e_3814_) == 6)
{
lean_object* v_binderName_3822_; lean_object* v_binderType_3823_; lean_object* v_body_3824_; lean_object* v___f_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_inc_n(v_toBind_3816_, 2);
v_binderName_3822_ = lean_ctor_get(v_e_3814_, 0);
lean_inc_n(v_binderName_3822_, 2);
v_binderType_3823_ = lean_ctor_get(v_e_3814_, 1);
lean_inc_ref(v_binderType_3823_);
v_body_3824_ = lean_ctor_get(v_e_3814_, 2);
lean_inc_ref(v_body_3824_);
lean_dec_ref_known(v_e_3814_, 3);
lean_inc(v_fieldVal_x3f_3812_);
v___f_3825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3825_, 0, v_toPure_3817_);
lean_closure_set(v___f_3825_, 1, v_usedFields_3813_);
lean_closure_set(v___f_3825_, 2, v_binderName_3822_);
lean_closure_set(v___f_3825_, 3, v_body_3824_);
lean_closure_set(v___f_3825_, 4, v_inst_3810_);
lean_closure_set(v___f_3825_, 5, v_inst_3811_);
lean_closure_set(v___f_3825_, 6, v_fieldVal_x3f_3812_);
lean_closure_set(v___f_3825_, 7, v_binderType_3823_);
lean_closure_set(v___f_3825_, 8, v_toBind_3816_);
v___x_3826_ = lean_apply_1(v_fieldVal_x3f_3812_, v_binderName_3822_);
v___x_3827_ = lean_apply_4(v_toBind_3816_, lean_box(0), lean_box(0), v___x_3826_, v___f_3825_);
return v___x_3827_;
}
else
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v_fieldVal_x3f_3812_);
lean_dec(v_inst_3811_);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_inst_3810_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; lean_object* v_unused_3846_; 
v_unused_3845_ = lean_ctor_get(v_inst_3810_, 1);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_inst_3810_, 0);
lean_dec(v_unused_3846_);
v___x_3829_ = v_inst_3810_;
v_isShared_3830_ = v_isSharedCheck_3844_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_inst_3810_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3844_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; uint8_t v___x_3832_; 
lean_inc_ref(v_e_3814_);
v___x_3831_ = l_Lean_Expr_cleanupAnnotations(v_e_3814_);
v___x_3832_ = l_Lean_Expr_isApp(v___x_3831_);
if (v___x_3832_ == 0)
{
lean_dec_ref(v___x_3831_);
lean_del_object(v___x_3829_);
goto v___jp_3818_;
}
else
{
lean_object* v_arg_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_arg_3833_ = lean_ctor_get(v___x_3831_, 1);
lean_inc_ref(v_arg_3833_);
v___x_3834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3831_);
v___x_3835_ = l_Lean_Expr_isApp(v___x_3834_);
if (v___x_3835_ == 0)
{
lean_dec_ref(v___x_3834_);
lean_dec_ref(v_arg_3833_);
lean_del_object(v___x_3829_);
goto v___jp_3818_;
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3836_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3834_);
v___x_3837_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3838_ = l_Lean_Expr_isConstOf(v___x_3836_, v___x_3837_);
lean_dec_ref(v___x_3836_);
if (v___x_3838_ == 0)
{
lean_dec_ref(v_arg_3833_);
lean_del_object(v___x_3829_);
goto v___jp_3818_;
}
else
{
lean_object* v___x_3840_; 
lean_dec_ref(v_e_3814_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v_arg_3833_);
lean_ctor_set(v___x_3829_, 0, v_usedFields_3813_);
v___x_3840_ = v___x_3829_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_usedFields_3813_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_arg_3833_);
v___x_3840_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
v___x_3842_ = lean_apply_2(v_toPure_3817_, lean_box(0), v___x_3841_);
return v___x_3842_;
}
}
}
}
}
}
v___jp_3818_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_usedFields_3813_);
lean_ctor_set(v___x_3819_, 1, v_e_3814_);
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = lean_apply_2(v_toPure_3817_, lean_box(0), v___x_3820_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3847_, lean_object* v_usedFields_3848_, lean_object* v_binderName_3849_, lean_object* v_body_3850_, lean_object* v_val_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_fieldVal_x3f_3854_, uint8_t v_____do__lift_3855_){
_start:
{
if (v_____do__lift_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec(v_fieldVal_x3f_3854_);
lean_dec(v_inst_3853_);
lean_dec_ref(v_inst_3852_);
lean_dec(v_binderName_3849_);
lean_dec(v_usedFields_3848_);
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_apply_2(v_toPure_3847_, lean_box(0), v___x_3856_);
return v___x_3857_;
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec(v_toPure_3847_);
v___x_3858_ = l_Lean_NameSet_insert(v_usedFields_3848_, v_binderName_3849_);
v___x_3859_ = lean_expr_instantiate1(v_body_3850_, v_val_3851_);
v___x_3860_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3852_, v_inst_3853_, v_fieldVal_x3f_3854_, v___x_3858_, v___x_3859_);
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_fieldVal_x3f_3864_, lean_object* v_usedFields_3865_, lean_object* v_e_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3862_, v_inst_3863_, v_fieldVal_x3f_3864_, v_usedFields_3865_, v_e_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3868_, lean_object* v_inst_3869_, lean_object* v_fieldVal_x3f_3870_, lean_object* v_toPure_3871_, lean_object* v_____s_3872_){
_start:
{
lean_object* v_fst_3873_; 
v_fst_3873_ = lean_ctor_get(v_____s_3872_, 0);
if (lean_obj_tag(v_fst_3873_) == 0)
{
lean_object* v_snd_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v_toPure_3871_);
v_snd_3874_ = lean_ctor_get(v_____s_3872_, 1);
lean_inc(v_snd_3874_);
lean_dec_ref(v_____s_3872_);
v___x_3875_ = l_Lean_NameSet_empty;
v___x_3876_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3868_, v_inst_3869_, v_fieldVal_x3f_3870_, v___x_3875_, v_snd_3874_);
return v___x_3876_;
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3878_; 
lean_inc_ref(v_fst_3873_);
lean_dec_ref(v_____s_3872_);
lean_dec(v_fieldVal_x3f_3870_);
lean_dec(v_inst_3869_);
lean_dec_ref(v_inst_3868_);
v_val_3877_ = lean_ctor_get(v_fst_3873_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_fst_3873_, 1);
v___x_3878_ = lean_apply_2(v_toPure_3871_, lean_box(0), v_val_3877_);
return v___x_3878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3879_, lean_object* v_a_3880_, lean_object* v___x_3881_, lean_object* v_toPure_3882_, lean_object* v_____r_3883_){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3884_ = lean_expr_instantiate1(v_body_3879_, v_a_3880_);
v___x_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3881_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
v___x_3887_ = lean_apply_2(v_toPure_3882_, lean_box(0), v___x_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3888_, lean_object* v_a_3889_, lean_object* v___x_3890_, lean_object* v_toPure_3891_, lean_object* v_____r_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3888_, v_a_3889_, v___x_3890_, v_toPure_3891_, v_____r_3892_);
lean_dec_ref(v_a_3889_);
lean_dec_ref(v_body_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3896_, lean_object* v_toPure_3897_, lean_object* v___f_3898_, uint8_t v_____do__lift_3899_){
_start:
{
if (v_____do__lift_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec(v___f_3898_);
v___x_3900_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v_snd_3896_);
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
v___x_3903_ = lean_apply_2(v_toPure_3897_, lean_box(0), v___x_3902_);
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec(v_toPure_3897_);
lean_dec(v_snd_3896_);
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_apply_1(v___f_3898_, v___x_3904_);
return v___x_3905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3906_, lean_object* v_toPure_3907_, lean_object* v___f_3908_, lean_object* v_____do__lift_3909_){
_start:
{
uint8_t v_____do__lift_560__boxed_3910_; lean_object* v_res_3911_; 
v_____do__lift_560__boxed_3910_ = lean_unbox(v_____do__lift_3909_);
v_res_3911_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3906_, v_toPure_3907_, v___f_3908_, v_____do__lift_560__boxed_3910_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3912_, lean_object* v_inst_3913_, lean_object* v_toBind_3914_, lean_object* v___f_3915_, lean_object* v_____do__lift_3916_){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3917_, 0, v_____do__lift_3916_);
lean_closure_set(v___x_3917_, 1, v_binderType_3912_);
v___x_3918_ = lean_apply_2(v_inst_3913_, lean_box(0), v___x_3917_);
v___x_3919_ = lean_apply_4(v_toBind_3914_, lean_box(0), lean_box(0), v___x_3918_, v___f_3915_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3920_, lean_object* v_toPure_3921_, lean_object* v_levels_x3f_3922_, lean_object* v_inst_3923_, lean_object* v_toBind_3924_, lean_object* v_a_3925_, lean_object* v_x_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_snd_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3948_; 
v_snd_3928_ = lean_ctor_get(v___y_3927_, 1);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___y_3927_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; 
v_unused_3949_ = lean_ctor_get(v___y_3927_, 0);
lean_dec(v_unused_3949_);
v___x_3930_ = v___y_3927_;
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_snd_3928_);
lean_dec(v___y_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3948_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
if (lean_obj_tag(v_snd_3928_) == 6)
{
lean_object* v_binderType_3932_; lean_object* v_body_3933_; lean_object* v___f_3934_; 
lean_del_object(v___x_3930_);
v_binderType_3932_ = lean_ctor_get(v_snd_3928_, 1);
lean_inc_ref(v_binderType_3932_);
v_body_3933_ = lean_ctor_get(v_snd_3928_, 2);
lean_inc(v_toPure_3921_);
lean_inc(v___x_3920_);
lean_inc_ref(v_a_3925_);
lean_inc_ref(v_body_3933_);
v___f_3934_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3934_, 0, v_body_3933_);
lean_closure_set(v___f_3934_, 1, v_a_3925_);
lean_closure_set(v___f_3934_, 2, v___x_3920_);
lean_closure_set(v___f_3934_, 3, v_toPure_3921_);
if (lean_obj_tag(v_levels_x3f_3922_) == 0)
{
lean_object* v___f_3935_; lean_object* v___f_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec(v___x_3920_);
v___f_3935_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3935_, 0, v_snd_3928_);
lean_closure_set(v___f_3935_, 1, v_toPure_3921_);
lean_closure_set(v___f_3935_, 2, v___f_3934_);
lean_inc(v_toBind_3924_);
lean_inc(v_inst_3923_);
v___f_3936_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3936_, 0, v_binderType_3932_);
lean_closure_set(v___f_3936_, 1, v_inst_3923_);
lean_closure_set(v___f_3936_, 2, v_toBind_3924_);
lean_closure_set(v___f_3936_, 3, v___f_3935_);
v___x_3937_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3937_, 0, v_a_3925_);
v___x_3938_ = lean_apply_2(v_inst_3923_, lean_box(0), v___x_3937_);
v___x_3939_ = lean_apply_4(v_toBind_3924_, lean_box(0), lean_box(0), v___x_3938_, v___f_3936_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
lean_inc_ref(v_body_3933_);
lean_dec_ref(v___f_3934_);
lean_dec_ref(v_binderType_3932_);
lean_dec_ref_known(v_snd_3928_, 3);
lean_dec(v_toBind_3924_);
lean_dec(v_inst_3923_);
v___x_3940_ = lean_box(0);
v___x_3941_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3933_, v_a_3925_, v___x_3920_, v_toPure_3921_, v___x_3940_);
lean_dec_ref(v_a_3925_);
lean_dec_ref(v_body_3933_);
return v___x_3941_;
}
}
else
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
lean_dec_ref(v_a_3925_);
lean_dec(v_toBind_3924_);
lean_dec(v_inst_3923_);
lean_dec(v___x_3920_);
v___x_3942_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3942_);
v___x_3944_ = v___x_3930_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_snd_3928_);
v___x_3944_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___x_3946_ = lean_apply_2(v_toPure_3921_, lean_box(0), v___x_3945_);
return v___x_3946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3950_, lean_object* v_toPure_3951_, lean_object* v_levels_x3f_3952_, lean_object* v_inst_3953_, lean_object* v_toBind_3954_, lean_object* v_a_3955_, lean_object* v_x_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3950_, v_toPure_3951_, v_levels_x3f_3952_, v_inst_3953_, v_toBind_3954_, v_a_3955_, v_x_3956_, v___y_3957_);
lean_dec(v_levels_x3f_3952_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3959_, lean_object* v_levels_x3f_3960_, lean_object* v_inst_3961_, lean_object* v_toBind_3962_, lean_object* v_params_3963_, lean_object* v_inst_3964_, lean_object* v___f_3965_, lean_object* v_val_3966_){
_start:
{
lean_object* v___x_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; size_t v_sz_3970_; size_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3967_ = lean_box(0);
lean_inc(v_toBind_3962_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3968_, 0, v___x_3967_);
lean_closure_set(v___f_3968_, 1, v_toPure_3959_);
lean_closure_set(v___f_3968_, 2, v_levels_x3f_3960_);
lean_closure_set(v___f_3968_, 3, v_inst_3961_);
lean_closure_set(v___f_3968_, 4, v_toBind_3962_);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v_val_3966_);
v_sz_3970_ = lean_array_size(v_params_3963_);
v___x_3971_ = ((size_t)0ULL);
v___x_3972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3964_, v_params_3963_, v___f_3968_, v_sz_3970_, v___x_3971_, v___x_3969_);
v___x_3973_ = lean_apply_4(v_toBind_3962_, lean_box(0), lean_box(0), v___x_3972_, v___f_3965_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3974_, lean_object* v_us_3975_, uint8_t v___x_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3974_, v_us_3975_, v___x_3976_, v___y_3979_, v___y_3980_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3983_, lean_object* v_us_3984_, lean_object* v___x_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
uint8_t v___x_671__boxed_3991_; lean_object* v_res_3992_; 
v___x_671__boxed_3991_ = lean_unbox(v___x_3985_);
v_res_3992_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3983_, v_us_3984_, v___x_671__boxed_3991_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec_ref(v_cinfo_3983_);
return v_res_3992_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3996_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_3997_ = lean_unsigned_to_nat(2u);
v___x_3998_ = lean_unsigned_to_nat(202u);
v___x_3999_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4000_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4001_ = l_mkPanicMessageWithDecl(v___x_4000_, v___x_3999_, v___x_3998_, v___x_3997_, v___x_3996_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4002_, lean_object* v___x_4003_, lean_object* v_inst_4004_, lean_object* v_toBind_4005_, lean_object* v___f_4006_, lean_object* v_us_4007_){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4008_ = l_List_lengthTR___redArg(v_us_4007_);
v___x_4009_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4002_);
v___x_4010_ = l_List_lengthTR___redArg(v___x_4009_);
lean_dec(v___x_4009_);
v___x_4011_ = lean_nat_dec_eq(v___x_4008_, v___x_4010_);
lean_dec(v___x_4010_);
lean_dec(v___x_4008_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_dec(v_us_4007_);
lean_dec(v___f_4006_);
lean_dec(v_toBind_4005_);
lean_dec(v_inst_4004_);
lean_dec_ref(v_cinfo_4002_);
v___x_4012_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4013_ = l_panic___redArg(v___x_4003_, v___x_4012_);
return v___x_4013_;
}
else
{
uint8_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___f_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4014_ = 0;
v___x_4015_ = lean_box(v___x_4014_);
v___f_4016_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4016_, 0, v_cinfo_4002_);
lean_closure_set(v___f_4016_, 1, v_us_4007_);
lean_closure_set(v___f_4016_, 2, v___x_4015_);
v___x_4017_ = lean_apply_2(v_inst_4004_, lean_box(0), v___f_4016_);
v___x_4018_ = lean_apply_4(v_toBind_4005_, lean_box(0), lean_box(0), v___x_4017_, v___f_4006_);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4019_, lean_object* v___x_4020_, lean_object* v_inst_4021_, lean_object* v_toBind_4022_, lean_object* v___f_4023_, lean_object* v_us_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4019_, v___x_4020_, v_inst_4021_, v_toBind_4022_, v___f_4023_, v_us_4024_);
lean_dec(v___x_4020_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4026_, lean_object* v_inst_4027_, lean_object* v_toBind_4028_, lean_object* v___f_4029_, lean_object* v_levels_x3f_4030_, lean_object* v_toPure_4031_, lean_object* v_cinfo_4032_){
_start:
{
lean_object* v___f_4033_; 
lean_inc(v_toBind_4028_);
lean_inc(v_inst_4027_);
lean_inc_ref(v_cinfo_4032_);
v___f_4033_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4033_, 0, v_cinfo_4032_);
lean_closure_set(v___f_4033_, 1, v___x_4026_);
lean_closure_set(v___f_4033_, 2, v_inst_4027_);
lean_closure_set(v___f_4033_, 3, v_toBind_4028_);
lean_closure_set(v___f_4033_, 4, v___f_4029_);
if (lean_obj_tag(v_levels_x3f_4030_) == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec(v_toPure_4031_);
v___x_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4034_, 0, v_cinfo_4032_);
v___x_4035_ = lean_apply_2(v_inst_4027_, lean_box(0), v___x_4034_);
v___x_4036_ = lean_apply_4(v_toBind_4028_, lean_box(0), lean_box(0), v___x_4035_, v___f_4033_);
return v___x_4036_;
}
else
{
lean_object* v_val_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v_cinfo_4032_);
lean_dec(v_inst_4027_);
v_val_4037_ = lean_ctor_get(v_levels_x3f_4030_, 0);
lean_inc(v_val_4037_);
lean_dec_ref_known(v_levels_x3f_4030_, 1);
v___x_4038_ = lean_apply_2(v_toPure_4031_, lean_box(0), v_val_4037_);
v___x_4039_ = lean_apply_4(v_toBind_4028_, lean_box(0), lean_box(0), v___x_4038_, v___f_4033_);
return v___x_4039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4040_, lean_object* v_inst_4041_, lean_object* v_inst_4042_, lean_object* v_inst_4043_, lean_object* v_defaultFn_4044_, lean_object* v_levels_x3f_4045_, lean_object* v_params_4046_, lean_object* v_fieldVal_x3f_4047_){
_start:
{
lean_object* v_toApplicative_4048_; lean_object* v_toBind_4049_; lean_object* v_toPure_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___f_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; lean_object* v___f_4056_; lean_object* v___x_4057_; 
v_toApplicative_4048_ = lean_ctor_get(v_inst_4040_, 0);
v_toBind_4049_ = lean_ctor_get(v_inst_4040_, 1);
lean_inc_n(v_toBind_4049_, 3);
v_toPure_4050_ = lean_ctor_get(v_toApplicative_4048_, 1);
lean_inc_n(v_toPure_4050_, 3);
v___x_4051_ = lean_box(0);
lean_inc_ref_n(v_inst_4040_, 3);
v___x_4052_ = l_Lean_getConstInfo___redArg(v_inst_4040_, v_inst_4041_, v_inst_4042_, v_defaultFn_4044_);
lean_inc_n(v_inst_4043_, 2);
v___f_4053_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4053_, 0, v_inst_4040_);
lean_closure_set(v___f_4053_, 1, v_inst_4043_);
lean_closure_set(v___f_4053_, 2, v_fieldVal_x3f_4047_);
lean_closure_set(v___f_4053_, 3, v_toPure_4050_);
lean_inc(v_levels_x3f_4045_);
v___f_4054_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4054_, 0, v_toPure_4050_);
lean_closure_set(v___f_4054_, 1, v_levels_x3f_4045_);
lean_closure_set(v___f_4054_, 2, v_inst_4043_);
lean_closure_set(v___f_4054_, 3, v_toBind_4049_);
lean_closure_set(v___f_4054_, 4, v_params_4046_);
lean_closure_set(v___f_4054_, 5, v_inst_4040_);
lean_closure_set(v___f_4054_, 6, v___f_4053_);
v___x_4055_ = l_instInhabitedOfMonad___redArg(v_inst_4040_, v___x_4051_);
v___f_4056_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4056_, 0, v___x_4055_);
lean_closure_set(v___f_4056_, 1, v_inst_4043_);
lean_closure_set(v___f_4056_, 2, v_toBind_4049_);
lean_closure_set(v___f_4056_, 3, v___f_4054_);
lean_closure_set(v___f_4056_, 4, v_levels_x3f_4045_);
lean_closure_set(v___f_4056_, 5, v_toPure_4050_);
v___x_4057_ = lean_apply_4(v_toBind_4049_, lean_box(0), lean_box(0), v___x_4052_, v___f_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4058_, lean_object* v_inst_4059_, lean_object* v_inst_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_, lean_object* v_inst_4063_, lean_object* v_defaultFn_4064_, lean_object* v_levels_x3f_4065_, lean_object* v_params_4066_, lean_object* v_fieldVal_x3f_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4059_, v_inst_4060_, v_inst_4061_, v_inst_4062_, v_defaultFn_4064_, v_levels_x3f_4065_, v_params_4066_, v_fieldVal_x3f_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4069_, lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_inst_4072_, lean_object* v_inst_4073_, lean_object* v_inst_4074_, lean_object* v_defaultFn_4075_, lean_object* v_levels_x3f_4076_, lean_object* v_params_4077_, lean_object* v_fieldVal_x3f_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4069_, v_inst_4070_, v_inst_4071_, v_inst_4072_, v_inst_4073_, v_inst_4074_, v_defaultFn_4075_, v_levels_x3f_4076_, v_params_4077_, v_fieldVal_x3f_4078_);
lean_dec_ref(v_inst_4074_);
return v_res_4079_;
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
