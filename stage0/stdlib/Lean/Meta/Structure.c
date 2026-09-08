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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__0));
v___x_50_ = l_Lean_stringToMessageData(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__2));
v___x_53_ = l_Lean_stringToMessageData(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__5(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__4));
v___x_56_ = l_Lean_stringToMessageData(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName(lean_object* v_struct_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Expr_getAppFn(v_struct_57_);
if (lean_obj_tag(v___x_63_) == 4)
{
lean_object* v_declName_64_; lean_object* v___x_65_; lean_object* v_env_66_; uint8_t v___x_67_; 
v_declName_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc_n(v_declName_64_, 2);
lean_dec_ref_known(v___x_63_, 2);
v___x_65_ = lean_st_ref_get(v_a_61_);
v_env_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc_ref(v_env_66_);
lean_dec(v___x_65_);
v___x_67_ = l_Lean_isStructure(v_env_66_, v_declName_64_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v___x_68_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_69_ = l_Lean_MessageData_ofConstName(v_declName_64_, v___x_67_);
v___x_70_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__3, &l_Lean_Meta_getStructureName___closed__3_once, _init_l_Lean_Meta_getStructureName___closed__3);
v___x_72_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_72_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_declName_64_);
return v___x_82_;
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v___x_63_);
v___x_83_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__5, &l_Lean_Meta_getStructureName___closed__5_once, _init_l_Lean_Meta_getStructureName___closed__5);
v___x_84_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_83_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName___boxed(lean_object* v_struct_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_getStructureName(v_struct_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec_ref(v_struct_85_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_object* v_00_u03b1_92_, lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(lean_object* v_00_u03b1_100_, lean_object* v_msg_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(v_00_u03b1_100_, v_msg_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(lean_object* v_name_108_, lean_object* v_levelParams_109_, lean_object* v_type_110_, lean_object* v_value_111_, lean_object* v_hints_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; uint8_t v___y_117_; uint8_t v___y_124_; lean_object* v_env_127_; uint8_t v___x_128_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_env_127_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref_n(v_env_127_, 2);
lean_dec(v___x_115_);
v___x_128_ = l_Lean_Environment_hasUnsafe(v_env_127_, v_type_110_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_Environment_hasUnsafe(v_env_127_, v_value_111_);
v___y_124_ = v___x_129_;
goto v___jp_123_;
}
else
{
lean_dec_ref(v_env_127_);
v___y_124_ = v___x_128_;
goto v___jp_123_;
}
v___jp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
lean_inc(v_name_108_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v_name_108_);
lean_ctor_set(v___x_118_, 1, v_levelParams_109_);
lean_ctor_set(v___x_118_, 2, v_type_110_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v_name_108_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_121_, 0, v___x_118_);
lean_ctor_set(v___x_121_, 1, v_value_111_);
lean_ctor_set(v___x_121_, 2, v_hints_112_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*4, v___y_117_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
v___y_117_ = v___x_125_;
goto v___jp_116_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
v___y_117_ = v___x_126_;
goto v___jp_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v_name_130_, lean_object* v_levelParams_131_, lean_object* v_type_132_, lean_object* v_value_133_, lean_object* v_hints_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_130_, v_levelParams_131_, v_type_132_, v_value_133_, v_hints_134_, v___y_135_);
lean_dec(v___y_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_name_138_, lean_object* v_levelParams_139_, lean_object* v_type_140_, lean_object* v_value_141_, lean_object* v_hints_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_138_, v_levelParams_139_, v_type_140_, v_value_141_, v_hints_142_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object* v_name_149_, lean_object* v_levelParams_150_, lean_object* v_type_151_, lean_object* v_value_152_, lean_object* v_hints_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_149_, v_levelParams_150_, v_type_151_, v_value_152_, v_hints_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v_k_160_, lean_object* v_b_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_167_ = lean_apply_6(v_k_160_, v_b_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, lean_box(0));
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_168_, v_b_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_name_176_, uint8_t v_bi_177_, lean_object* v_type_178_, lean_object* v_k_179_, uint8_t v_kind_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___f_186_; lean_object* v___x_187_; 
v___f_186_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_186_, 0, v_k_179_);
v___x_187_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_176_, v_bi_177_, v_type_178_, v___f_186_, v_kind_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_187_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_187_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object* v_name_204_, lean_object* v_bi_205_, lean_object* v_type_206_, lean_object* v_k_207_, lean_object* v_kind_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v_bi_boxed_214_; uint8_t v_kind_boxed_215_; lean_object* v_res_216_; 
v_bi_boxed_214_ = lean_unbox(v_bi_205_);
v_kind_boxed_215_ = lean_unbox(v_kind_208_);
v_res_216_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_204_, v_bi_boxed_214_, v_type_206_, v_k_207_, v_kind_boxed_215_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_00_u03b1_217_, lean_object* v_name_218_, uint8_t v_bi_219_, lean_object* v_type_220_, lean_object* v_k_221_, uint8_t v_kind_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_218_, v_bi_219_, v_type_220_, v_k_221_, v_kind_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object* v_00_u03b1_229_, lean_object* v_name_230_, lean_object* v_bi_231_, lean_object* v_type_232_, lean_object* v_k_233_, lean_object* v_kind_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_bi_boxed_240_; uint8_t v_kind_boxed_241_; lean_object* v_res_242_; 
v_bi_boxed_240_ = lean_unbox(v_bi_231_);
v_kind_boxed_241_ = lean_unbox(v_kind_234_);
v_res_242_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(v_00_u03b1_229_, v_name_230_, v_bi_boxed_240_, v_type_232_, v_k_233_, v_kind_boxed_241_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_243_, lean_object* v_b_244_, lean_object* v_c_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; 
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
v___x_251_ = lean_apply_7(v_k_243_, v_b_244_, v_c_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_252_, lean_object* v_b_253_, lean_object* v_c_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_252_, v_b_253_, v_c_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_type_261_, lean_object* v_maxFVars_x3f_262_, lean_object* v_k_263_, uint8_t v_cleanupAnnotations_264_, uint8_t v_whnfType_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___f_271_; lean_object* v___x_272_; 
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_271_, 0, v_k_263_);
v___x_272_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_261_, v_maxFVars_x3f_262_, v___f_271_, v_cleanupAnnotations_264_, v_whnfType_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_272_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_272_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_type_289_, lean_object* v_maxFVars_x3f_290_, lean_object* v_k_291_, lean_object* v_cleanupAnnotations_292_, lean_object* v_whnfType_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_299_; uint8_t v_whnfType_boxed_300_; lean_object* v_res_301_; 
v_cleanupAnnotations_boxed_299_ = lean_unbox(v_cleanupAnnotations_292_);
v_whnfType_boxed_300_ = lean_unbox(v_whnfType_293_);
v_res_301_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_289_, v_maxFVars_x3f_290_, v_k_291_, v_cleanupAnnotations_boxed_299_, v_whnfType_boxed_300_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_302_, lean_object* v_type_303_, lean_object* v_maxFVars_x3f_304_, lean_object* v_k_305_, uint8_t v_cleanupAnnotations_306_, uint8_t v_whnfType_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_303_, v_maxFVars_x3f_304_, v_k_305_, v_cleanupAnnotations_306_, v_whnfType_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_314_, lean_object* v_type_315_, lean_object* v_maxFVars_x3f_316_, lean_object* v_k_317_, lean_object* v_cleanupAnnotations_318_, lean_object* v_whnfType_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_325_; uint8_t v_whnfType_boxed_326_; lean_object* v_res_327_; 
v_cleanupAnnotations_boxed_325_ = lean_unbox(v_cleanupAnnotations_318_);
v_whnfType_boxed_326_ = lean_unbox(v_whnfType_319_);
v_res_327_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_314_, v_type_315_, v_maxFVars_x3f_316_, v_k_317_, v_cleanupAnnotations_boxed_325_, v_whnfType_boxed_326_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_lctx_328_, lean_object* v_localInsts_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_328_, v_localInsts_329_, v_x_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_lctx_353_, lean_object* v_localInsts_354_, lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_353_, v_localInsts_354_, v_x_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_362_, lean_object* v_lctx_363_, lean_object* v_localInsts_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_363_, v_localInsts_364_, v_x_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_372_, lean_object* v_lctx_373_, lean_object* v_localInsts_374_, lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_372_, v_lctx_373_, v_localInsts_374_, v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_toCold_389_; lean_object* v_currRecDepth_390_; lean_object* v_ref_391_; uint8_t v_diag_392_; uint8_t v_suppressElabErrors_393_; lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_toCold_389_ = lean_ctor_get(v___y_386_, 0);
v_currRecDepth_390_ = lean_ctor_get(v___y_386_, 1);
v_ref_391_ = lean_ctor_get(v___y_386_, 2);
v_diag_392_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*3);
v_suppressElabErrors_393_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*3 + 1);
v_ref_394_ = l_Lean_replaceRef(v_ref_382_, v_ref_391_);
lean_inc(v_currRecDepth_390_);
lean_inc_ref(v_toCold_389_);
v___x_395_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_395_, 0, v_toCold_389_);
lean_ctor_set(v___x_395_, 1, v_currRecDepth_390_);
lean_ctor_set(v___x_395_, 2, v_ref_394_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3, v_diag_392_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3 + 1, v_suppressElabErrors_393_);
v___x_396_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_, v___x_395_, v___y_387_);
lean_dec_ref_known(v___x_395_, 3);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_397_, lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_397_, v_msg_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v_ref_397_);
return v_res_404_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_414_, lean_object* v_projName_415_, lean_object* v_n_416_, lean_object* v_ref_417_, lean_object* v___f_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
if (v___x_414_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_424_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_425_ = l_Lean_MessageData_ofName(v_projName_415_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_MessageData_ofConstName(v_n_416_, v___x_414_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_417_, v___x_432_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
v___x_435_ = lean_apply_6(v___f_418_, v_a_434_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
return v___x_435_;
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec_ref(v___f_418_);
v_a_436_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_433_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_433_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v_n_416_);
lean_dec(v_projName_415_);
v___x_444_ = lean_box(0);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
v___x_445_ = lean_apply_6(v___f_418_, v___x_444_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, lean_box(0));
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_446_, lean_object* v_projName_447_, lean_object* v_n_448_, lean_object* v_ref_449_, lean_object* v___f_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_16906__boxed_456_; lean_object* v_res_457_; 
v___x_16906__boxed_456_ = lean_unbox(v___x_446_);
v_res_457_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_16906__boxed_456_, v_projName_447_, v_n_448_, v_ref_449_, v___f_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v_ref_449_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_458_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_464_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_ctor_set(v___x_464_, 4, v___x_463_);
lean_ctor_set(v___x_464_, 5, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_465_, uint8_t v_s_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v_env_471_; lean_object* v_nextMacroScope_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_traceState_475_; lean_object* v_messages_476_; lean_object* v_infoState_477_; lean_object* v_snapshotTasks_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_507_; 
v___x_470_ = lean_st_ref_take(v___y_468_);
v_env_471_ = lean_ctor_get(v___x_470_, 0);
v_nextMacroScope_472_ = lean_ctor_get(v___x_470_, 1);
v_ngen_473_ = lean_ctor_get(v___x_470_, 2);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_470_, 3);
v_traceState_475_ = lean_ctor_get(v___x_470_, 4);
v_messages_476_ = lean_ctor_get(v___x_470_, 6);
v_infoState_477_ = lean_ctor_get(v___x_470_, 7);
v_snapshotTasks_478_ = lean_ctor_get(v___x_470_, 8);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_470_, 5);
lean_dec(v_unused_508_);
v___x_480_ = v___x_470_;
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snapshotTasks_478_);
lean_inc(v_infoState_477_);
lean_inc(v_messages_476_);
lean_inc(v_traceState_475_);
lean_inc(v_auxDeclNGen_474_);
lean_inc(v_ngen_473_);
lean_inc(v_nextMacroScope_472_);
lean_inc(v_env_471_);
lean_dec(v___x_470_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_507_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_482_ = 0;
v___x_483_ = lean_box(0);
v___x_484_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_471_, v_declName_465_, v_s_466_, v___x_482_, v___x_483_);
v___x_485_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 5, v___x_485_);
lean_ctor_set(v___x_480_, 0, v___x_484_);
v___x_487_ = v___x_480_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_nextMacroScope_472_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_ngen_473_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_auxDeclNGen_474_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_traceState_475_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_messages_476_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_infoState_477_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_snapshotTasks_478_);
v___x_487_ = v_reuseFailAlloc_506_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_mctx_490_; lean_object* v_zetaDeltaFVarIds_491_; lean_object* v_postponed_492_; lean_object* v_diag_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_504_; 
v___x_488_ = lean_st_ref_put(v___y_468_, v___x_487_);
v___x_489_ = lean_st_ref_take(v___y_467_);
v_mctx_490_ = lean_ctor_get(v___x_489_, 0);
v_zetaDeltaFVarIds_491_ = lean_ctor_get(v___x_489_, 2);
v_postponed_492_ = lean_ctor_get(v___x_489_, 3);
v_diag_493_ = lean_ctor_get(v___x_489_, 4);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_489_, 1);
lean_dec(v_unused_505_);
v___x_495_ = v___x_489_;
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_diag_493_);
lean_inc(v_postponed_492_);
lean_inc(v_zetaDeltaFVarIds_491_);
lean_inc(v_mctx_490_);
lean_dec(v___x_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_504_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_mctx_490_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_zetaDeltaFVarIds_491_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_postponed_492_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_diag_493_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_st_ref_put(v___y_467_, v___x_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_509_, lean_object* v_s_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v_s_boxed_514_; lean_object* v_res_515_; 
v_s_boxed_514_ = lean_unbox(v_s_510_);
v_res_515_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_509_, v_s_boxed_514_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec(v___y_511_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
uint8_t v___x_522_; lean_object* v___x_523_; 
v___x_522_ = 0;
v___x_523_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_516_, v___x_522_, v___y_518_, v___y_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_540_, lean_object* v_projName_541_, lean_object* v___x_542_, lean_object* v_a_543_, uint8_t v_instImplicit_544_, lean_object* v___x_545_, lean_object* v_params_546_, lean_object* v_self_547_, lean_object* v_b_548_, uint8_t v___x_549_, lean_object* v_a_550_, lean_object* v___x_551_, lean_object* v_paramInfoOverrides_552_, lean_object* v_n_553_, lean_object* v_ref_554_, lean_object* v___x_555_, uint8_t v_a_556_, lean_object* v_____r_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_621_; uint8_t v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_List_lengthTR___redArg(v_paramInfoOverrides_552_);
v___x_716_ = lean_array_get_size(v_params_546_);
v___x_717_ = lean_nat_dec_le(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_541_);
v___x_719_ = l_Lean_MessageData_ofName(v_projName_541_);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_720_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
lean_inc(v_n_553_);
v___x_723_ = l_Lean_MessageData_ofConstName(v_n_553_, v___x_717_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_554_, v___x_726_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_dec_ref_known(v___x_727_, 1);
goto v___jp_676_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v___x_555_);
lean_dec(v_n_553_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_self_547_);
lean_dec(v___x_545_);
lean_dec(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v_projName_541_);
lean_dec_ref(v___x_540_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
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
else
{
goto v___jp_676_;
}
v___jp_563_:
{
lean_object* v___x_566_; lean_object* v_env_567_; lean_object* v_nextMacroScope_568_; lean_object* v_ngen_569_; lean_object* v_auxDeclNGen_570_; lean_object* v_traceState_571_; lean_object* v_messages_572_; lean_object* v_infoState_573_; lean_object* v_snapshotTasks_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_606_; 
v___x_566_ = lean_st_ref_take(v___y_564_);
v_env_567_ = lean_ctor_get(v___x_566_, 0);
v_nextMacroScope_568_ = lean_ctor_get(v___x_566_, 1);
v_ngen_569_ = lean_ctor_get(v___x_566_, 2);
v_auxDeclNGen_570_ = lean_ctor_get(v___x_566_, 3);
v_traceState_571_ = lean_ctor_get(v___x_566_, 4);
v_messages_572_ = lean_ctor_get(v___x_566_, 6);
v_infoState_573_ = lean_ctor_get(v___x_566_, 7);
v_snapshotTasks_574_ = lean_ctor_get(v___x_566_, 8);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_566_, 5);
lean_dec(v_unused_607_);
v___x_576_ = v___x_566_;
v_isShared_577_ = v_isSharedCheck_606_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snapshotTasks_574_);
lean_inc(v_infoState_573_);
lean_inc(v_messages_572_);
lean_inc(v_traceState_571_);
lean_inc(v_auxDeclNGen_570_);
lean_inc(v_ngen_569_);
lean_inc(v_nextMacroScope_568_);
lean_inc(v_env_567_);
lean_dec(v___x_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_606_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_name_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v_name_578_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_name_578_);
lean_dec_ref(v___x_540_);
lean_inc(v_projName_541_);
v___x_579_ = l_Lean_addProjectionFnInfo(v_env_567_, v_projName_541_, v_name_578_, v___x_542_, v_a_543_, v_instImplicit_544_);
v___x_580_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 5, v___x_580_);
lean_ctor_set(v___x_576_, 0, v___x_579_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_nextMacroScope_568_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_ngen_569_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_auxDeclNGen_570_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_traceState_571_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_messages_572_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_infoState_573_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_snapshotTasks_574_);
v___x_582_ = v_reuseFailAlloc_605_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_mctx_585_; lean_object* v_zetaDeltaFVarIds_586_; lean_object* v_postponed_587_; lean_object* v_diag_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_603_; 
v___x_583_ = lean_st_ref_put(v___y_564_, v___x_582_);
v___x_584_ = lean_st_ref_take(v___y_565_);
v_mctx_585_ = lean_ctor_get(v___x_584_, 0);
v_zetaDeltaFVarIds_586_ = lean_ctor_get(v___x_584_, 2);
v_postponed_587_ = lean_ctor_get(v___x_584_, 3);
v_diag_588_ = lean_ctor_get(v___x_584_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_604_);
v___x_590_ = v___x_584_;
v_isShared_591_ = v_isSharedCheck_603_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_diag_588_);
lean_inc(v_postponed_587_);
lean_inc(v_zetaDeltaFVarIds_586_);
lean_inc(v_mctx_585_);
lean_dec(v___x_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_603_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_mctx_585_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_zetaDeltaFVarIds_586_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_postponed_587_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_diag_588_);
v___x_594_ = v_reuseFailAlloc_602_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_st_ref_put(v___y_565_, v___x_594_);
v___x_596_ = l_Lean_Expr_const___override(v_projName_541_, v___x_545_);
v___x_597_ = l_Lean_mkAppN(v___x_596_, v_params_546_);
v___x_598_ = l_Lean_Expr_app___override(v___x_597_, v_self_547_);
v___x_599_ = l_Lean_Expr_bindingBody_x21(v_b_548_);
v___x_600_ = lean_expr_instantiate1(v___x_599_, v___x_598_);
lean_dec_ref(v___x_598_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
}
}
v___jp_608_:
{
if (lean_obj_tag(v___y_611_) == 0)
{
lean_dec_ref_known(v___y_611_, 1);
v___y_564_ = v___y_609_;
v___y_565_ = v___y_610_;
goto v___jp_563_;
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_self_547_);
lean_dec(v___x_545_);
lean_dec(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v_projName_541_);
lean_dec_ref(v___x_540_);
v_a_612_ = lean_ctor_get(v___y_611_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___y_611_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___y_611_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___y_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
v___jp_620_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_627_ = lean_box(0);
lean_inc(v_projName_541_);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_projName_541_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_629_, 0, v___y_623_);
lean_ctor_set(v___x_629_, 1, v___y_626_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*3, v___x_549_);
v___x_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = l_Lean_addDecl(v___x_630_, v___y_622_, v___y_624_, v___y_621_);
lean_dec_ref(v___y_624_);
v___y_609_ = v___y_621_;
v___y_610_ = v___y_625_;
v___y_611_ = v___x_631_;
goto v___jp_608_;
}
v___jp_632_:
{
uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v_toCold_641_; lean_object* v_currRecDepth_642_; lean_object* v_ref_643_; uint8_t v_diag_644_; uint8_t v_suppressElabErrors_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_ref_650_; lean_object* v___x_651_; 
v___x_639_ = 0;
lean_inc_ref(v_a_550_);
v___x_640_ = l_Lean_LocalContext_mkForall(v_a_550_, v___x_551_, v___y_634_, v___x_549_, v___x_639_);
lean_dec_ref(v___y_634_);
v_toCold_641_ = lean_ctor_get(v___y_637_, 0);
v_currRecDepth_642_ = lean_ctor_get(v___y_637_, 1);
v_ref_643_ = lean_ctor_get(v___y_637_, 2);
v_diag_644_ = lean_ctor_get_uint8(v___y_637_, sizeof(void*)*3);
v_suppressElabErrors_645_ = lean_ctor_get_uint8(v___y_637_, sizeof(void*)*3 + 1);
v___x_646_ = l_Lean_Expr_inferImplicit(v___x_640_, v___x_542_, v___x_549_);
v___x_647_ = l_Lean_Expr_updateForallBinderInfos(v___x_646_, v_paramInfoOverrides_552_);
lean_inc_ref(v_self_547_);
lean_inc(v_a_543_);
v___x_648_ = l_Lean_Expr_proj___override(v_n_553_, v_a_543_, v_self_547_);
v___x_649_ = l_Lean_LocalContext_mkLambda(v_a_550_, v___x_551_, v___x_648_, v___x_549_, v___x_639_);
lean_dec_ref(v___x_648_);
v_ref_650_ = l_Lean_replaceRef(v_ref_554_, v_ref_643_);
lean_inc(v_currRecDepth_642_);
lean_inc_ref(v_toCold_641_);
v___x_651_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_651_, 0, v_toCold_641_);
lean_ctor_set(v___x_651_, 1, v_currRecDepth_642_);
lean_ctor_set(v___x_651_, 2, v_ref_650_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*3, v_diag_644_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*3 + 1, v_suppressElabErrors_645_);
if (v___y_633_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_box(1);
lean_inc(v_projName_541_);
v___x_653_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_541_, v___x_555_, v___x_647_, v___x_649_, v___x_652_, v___y_638_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_a_654_);
v___x_656_ = l_Lean_addDecl(v___x_655_, v___x_639_, v___x_651_, v___y_638_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_dec_ref_known(v___x_656_, 1);
if (v_instImplicit_544_ == 0)
{
lean_object* v___x_657_; 
lean_inc(v_projName_541_);
v___x_657_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_541_, v___y_635_, v___y_636_, v___x_651_, v___y_638_);
lean_dec_ref_known(v___x_651_, 3);
v___y_609_ = v___y_638_;
v___y_610_ = v___y_636_;
v___y_611_ = v___x_657_;
goto v___jp_608_;
}
else
{
lean_dec_ref_known(v___x_651_, 3);
v___y_564_ = v___y_638_;
v___y_565_ = v___y_636_;
goto v___jp_563_;
}
}
else
{
lean_dec_ref_known(v___x_651_, 3);
v___y_609_ = v___y_638_;
v___y_610_ = v___y_636_;
v___y_611_ = v___x_656_;
goto v___jp_608_;
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref_known(v___x_651_, 3);
lean_dec_ref(v_self_547_);
lean_dec(v___x_545_);
lean_dec(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v_projName_541_);
lean_dec_ref(v___x_540_);
v_a_658_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_653_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_st_ref_get(v___y_638_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref_n(v_env_667_, 2);
lean_dec(v___x_666_);
lean_inc_ref(v___x_647_);
lean_inc(v_projName_541_);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v_projName_541_);
lean_ctor_set(v___x_668_, 1, v___x_555_);
lean_ctor_set(v___x_668_, 2, v___x_647_);
v___x_669_ = l_Lean_Environment_hasUnsafe(v_env_667_, v___x_647_);
lean_dec_ref(v___x_647_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
v___x_670_ = l_Lean_Environment_hasUnsafe(v_env_667_, v___x_649_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_671_ = lean_box(0);
lean_inc(v_projName_541_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v_projName_541_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_668_);
lean_ctor_set(v___x_673_, 1, v___x_649_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
v___x_674_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
v___x_675_ = l_Lean_addDecl(v___x_674_, v___x_639_, v___x_651_, v___y_638_);
lean_dec_ref_known(v___x_651_, 3);
v___y_609_ = v___y_638_;
v___y_610_ = v___y_636_;
v___y_611_ = v___x_675_;
goto v___jp_608_;
}
else
{
v___y_621_ = v___y_638_;
v___y_622_ = v___x_639_;
v___y_623_ = v___x_668_;
v___y_624_ = v___x_651_;
v___y_625_ = v___y_636_;
v___y_626_ = v___x_649_;
goto v___jp_620_;
}
}
else
{
lean_dec_ref(v_env_667_);
v___y_621_ = v___y_638_;
v___y_622_ = v___x_639_;
v___y_623_ = v___x_668_;
v___y_624_ = v___x_651_;
v___y_625_ = v___y_636_;
v___y_626_ = v___x_649_;
goto v___jp_620_;
}
}
}
v___jp_676_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = l_Lean_Expr_bindingDomain_x21(v_b_548_);
v___x_678_ = lean_expr_consume_type_annotations(v___x_677_);
lean_inc_ref(v___x_678_);
v___x_679_ = l_Lean_Meta_isProp(v___x_678_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_679_) == 0)
{
if (v_a_556_ == 0)
{
lean_object* v_a_680_; uint8_t v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_633_ = v___x_681_;
v___y_634_ = v___x_678_;
v___y_635_ = v___y_558_;
v___y_636_ = v___y_559_;
v___y_637_ = v___y_560_;
v___y_638_ = v___y_561_;
goto v___jp_632_;
}
else
{
lean_object* v_a_682_; uint8_t v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_679_, 1);
v___x_683_ = lean_unbox(v_a_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_541_);
v___x_685_ = l_Lean_MessageData_ofName(v_projName_541_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_unbox(v_a_682_);
lean_inc(v_n_553_);
v___x_690_ = l_Lean_MessageData_ofConstName(v_n_553_, v___x_689_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_688_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
lean_inc_ref(v___x_678_);
v___x_694_ = l_Lean_indentExpr(v___x_678_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_554_, v___x_695_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_696_) == 0)
{
uint8_t v___x_697_; 
lean_dec_ref_known(v___x_696_, 1);
v___x_697_ = lean_unbox(v_a_682_);
lean_dec(v_a_682_);
v___y_633_ = v___x_697_;
v___y_634_ = v___x_678_;
v___y_635_ = v___y_558_;
v___y_636_ = v___y_559_;
v___y_637_ = v___y_560_;
v___y_638_ = v___y_561_;
goto v___jp_632_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_a_682_);
lean_dec_ref(v___x_678_);
lean_dec(v___x_555_);
lean_dec(v_n_553_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_self_547_);
lean_dec(v___x_545_);
lean_dec(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v_projName_541_);
lean_dec_ref(v___x_540_);
v_a_698_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
uint8_t v___x_706_; 
v___x_706_ = lean_unbox(v_a_682_);
lean_dec(v_a_682_);
v___y_633_ = v___x_706_;
v___y_634_ = v___x_678_;
v___y_635_ = v___y_558_;
v___y_636_ = v___y_559_;
v___y_637_ = v___y_560_;
v___y_638_ = v___y_561_;
goto v___jp_632_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___x_678_);
lean_dec(v___x_555_);
lean_dec(v_n_553_);
lean_dec_ref(v_a_550_);
lean_dec_ref(v_self_547_);
lean_dec(v___x_545_);
lean_dec(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v_projName_541_);
lean_dec_ref(v___x_540_);
v_a_707_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_679_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_679_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_736_ = _args[0];
lean_object* v_projName_737_ = _args[1];
lean_object* v___x_738_ = _args[2];
lean_object* v_a_739_ = _args[3];
lean_object* v_instImplicit_740_ = _args[4];
lean_object* v___x_741_ = _args[5];
lean_object* v_params_742_ = _args[6];
lean_object* v_self_743_ = _args[7];
lean_object* v_b_744_ = _args[8];
lean_object* v___x_745_ = _args[9];
lean_object* v_a_746_ = _args[10];
lean_object* v___x_747_ = _args[11];
lean_object* v_paramInfoOverrides_748_ = _args[12];
lean_object* v_n_749_ = _args[13];
lean_object* v_ref_750_ = _args[14];
lean_object* v___x_751_ = _args[15];
lean_object* v_a_752_ = _args[16];
lean_object* v_____r_753_ = _args[17];
lean_object* v___y_754_ = _args[18];
lean_object* v___y_755_ = _args[19];
lean_object* v___y_756_ = _args[20];
lean_object* v___y_757_ = _args[21];
lean_object* v___y_758_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_759_; uint8_t v___x_17145__boxed_760_; uint8_t v_a_17151__boxed_761_; lean_object* v_res_762_; 
v_instImplicit_boxed_759_ = lean_unbox(v_instImplicit_740_);
v___x_17145__boxed_760_ = lean_unbox(v___x_745_);
v_a_17151__boxed_761_ = lean_unbox(v_a_752_);
v_res_762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_736_, v_projName_737_, v___x_738_, v_a_739_, v_instImplicit_boxed_759_, v___x_741_, v_params_742_, v_self_743_, v_b_744_, v___x_17145__boxed_760_, v_a_746_, v___x_747_, v_paramInfoOverrides_748_, v_n_749_, v_ref_750_, v___x_751_, v_a_17151__boxed_761_, v_____r_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v_ref_750_);
lean_dec(v_paramInfoOverrides_748_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v_b_744_);
lean_dec_ref(v_params_742_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_763_, uint8_t v_isExporting_764_, lean_object* v___x_765_, lean_object* v___y_766_, lean_object* v___x_767_, lean_object* v_a_x3f_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_env_771_; lean_object* v_nextMacroScope_772_; lean_object* v_ngen_773_; lean_object* v_auxDeclNGen_774_; lean_object* v_traceState_775_; lean_object* v_messages_776_; lean_object* v_infoState_777_; lean_object* v_snapshotTasks_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_803_; 
v___x_770_ = lean_st_ref_take(v___y_763_);
v_env_771_ = lean_ctor_get(v___x_770_, 0);
v_nextMacroScope_772_ = lean_ctor_get(v___x_770_, 1);
v_ngen_773_ = lean_ctor_get(v___x_770_, 2);
v_auxDeclNGen_774_ = lean_ctor_get(v___x_770_, 3);
v_traceState_775_ = lean_ctor_get(v___x_770_, 4);
v_messages_776_ = lean_ctor_get(v___x_770_, 6);
v_infoState_777_ = lean_ctor_get(v___x_770_, 7);
v_snapshotTasks_778_ = lean_ctor_get(v___x_770_, 8);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_770_, 5);
lean_dec(v_unused_804_);
v___x_780_ = v___x_770_;
v_isShared_781_ = v_isSharedCheck_803_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snapshotTasks_778_);
lean_inc(v_infoState_777_);
lean_inc(v_messages_776_);
lean_inc(v_traceState_775_);
lean_inc(v_auxDeclNGen_774_);
lean_inc(v_ngen_773_);
lean_inc(v_nextMacroScope_772_);
lean_inc(v_env_771_);
lean_dec(v___x_770_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_803_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_Environment_setExporting(v_env_771_, v_isExporting_764_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 5, v___x_765_);
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_nextMacroScope_772_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_ngen_773_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_auxDeclNGen_774_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_traceState_775_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_802_, 6, v_messages_776_);
lean_ctor_set(v_reuseFailAlloc_802_, 7, v_infoState_777_);
lean_ctor_set(v_reuseFailAlloc_802_, 8, v_snapshotTasks_778_);
v___x_784_ = v_reuseFailAlloc_802_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_mctx_787_; lean_object* v_zetaDeltaFVarIds_788_; lean_object* v_postponed_789_; lean_object* v_diag_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_800_; 
v___x_785_ = lean_st_ref_put(v___y_763_, v___x_784_);
v___x_786_ = lean_st_ref_take(v___y_766_);
v_mctx_787_ = lean_ctor_get(v___x_786_, 0);
v_zetaDeltaFVarIds_788_ = lean_ctor_get(v___x_786_, 2);
v_postponed_789_ = lean_ctor_get(v___x_786_, 3);
v_diag_790_ = lean_ctor_get(v___x_786_, 4);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_786_, 1);
lean_dec(v_unused_801_);
v___x_792_ = v___x_786_;
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_diag_790_);
lean_inc(v_postponed_789_);
lean_inc(v_zetaDeltaFVarIds_788_);
lean_inc(v_mctx_787_);
lean_dec(v___x_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_800_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_767_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_mctx_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_zetaDeltaFVarIds_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_postponed_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_diag_790_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_st_ref_put(v___y_766_, v___x_795_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_805_, lean_object* v_isExporting_806_, lean_object* v___x_807_, lean_object* v___y_808_, lean_object* v___x_809_, lean_object* v_a_x3f_810_, lean_object* v___y_811_){
_start:
{
uint8_t v_isExporting_boxed_812_; lean_object* v_res_813_; 
v_isExporting_boxed_812_ = lean_unbox(v_isExporting_806_);
v_res_813_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_805_, v_isExporting_boxed_812_, v___x_807_, v___y_808_, v___x_809_, v_a_x3f_810_);
lean_dec(v_a_x3f_810_);
lean_dec(v___y_808_);
lean_dec(v___y_805_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_814_, uint8_t v_isExporting_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; lean_object* v_env_822_; lean_object* v___x_823_; uint8_t v_isModule_824_; 
v___x_821_ = lean_st_ref_get(v___y_819_);
v_env_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc_ref(v_env_822_);
lean_dec(v___x_821_);
v___x_823_ = l_Lean_Environment_header(v_env_822_);
v_isModule_824_ = lean_ctor_get_uint8(v___x_823_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_823_);
if (v_isModule_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec_ref(v_env_822_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_825_ = lean_apply_5(v_x_814_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
return v___x_825_;
}
else
{
uint8_t v_isExporting_826_; 
v_isExporting_826_ = lean_ctor_get_uint8(v_env_822_, sizeof(void*)*8);
lean_dec_ref(v_env_822_);
if (v_isExporting_815_ == 0)
{
if (v_isExporting_826_ == 0)
{
lean_object* v___x_892_; 
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_892_ = lean_apply_5(v_x_814_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
return v___x_892_;
}
else
{
goto v___jp_827_;
}
}
else
{
if (v_isExporting_826_ == 0)
{
goto v___jp_827_;
}
else
{
lean_object* v___x_893_; 
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v___x_893_ = lean_apply_5(v_x_814_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
return v___x_893_;
}
}
v___jp_827_:
{
lean_object* v___x_828_; lean_object* v_env_829_; lean_object* v_nextMacroScope_830_; lean_object* v_ngen_831_; lean_object* v_auxDeclNGen_832_; lean_object* v_traceState_833_; lean_object* v_messages_834_; lean_object* v_infoState_835_; lean_object* v_snapshotTasks_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_890_; 
v___x_828_ = lean_st_ref_take(v___y_819_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
v_nextMacroScope_830_ = lean_ctor_get(v___x_828_, 1);
v_ngen_831_ = lean_ctor_get(v___x_828_, 2);
v_auxDeclNGen_832_ = lean_ctor_get(v___x_828_, 3);
v_traceState_833_ = lean_ctor_get(v___x_828_, 4);
v_messages_834_ = lean_ctor_get(v___x_828_, 6);
v_infoState_835_ = lean_ctor_get(v___x_828_, 7);
v_snapshotTasks_836_ = lean_ctor_get(v___x_828_, 8);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_828_, 5);
lean_dec(v_unused_891_);
v___x_838_ = v___x_828_;
v_isShared_839_ = v_isSharedCheck_890_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snapshotTasks_836_);
lean_inc(v_infoState_835_);
lean_inc(v_messages_834_);
lean_inc(v_traceState_833_);
lean_inc(v_auxDeclNGen_832_);
lean_inc(v_ngen_831_);
lean_inc(v_nextMacroScope_830_);
lean_inc(v_env_829_);
lean_dec(v___x_828_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_890_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = l_Lean_Environment_setExporting(v_env_829_, v_isExporting_815_);
v___x_841_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 5, v___x_841_);
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_nextMacroScope_830_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_ngen_831_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_auxDeclNGen_832_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_traceState_833_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_messages_834_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_infoState_835_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v_snapshotTasks_836_);
v___x_843_ = v_reuseFailAlloc_889_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_mctx_846_; lean_object* v_zetaDeltaFVarIds_847_; lean_object* v_postponed_848_; lean_object* v_diag_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_887_; 
v___x_844_ = lean_st_ref_put(v___y_819_, v___x_843_);
v___x_845_ = lean_st_ref_take(v___y_817_);
v_mctx_846_ = lean_ctor_get(v___x_845_, 0);
v_zetaDeltaFVarIds_847_ = lean_ctor_get(v___x_845_, 2);
v_postponed_848_ = lean_ctor_get(v___x_845_, 3);
v_diag_849_ = lean_ctor_get(v___x_845_, 4);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v___x_845_, 1);
lean_dec(v_unused_888_);
v___x_851_ = v___x_845_;
v_isShared_852_ = v_isSharedCheck_887_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_diag_849_);
lean_inc(v_postponed_848_);
lean_inc(v_zetaDeltaFVarIds_847_);
lean_inc(v_mctx_846_);
lean_dec(v___x_845_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_887_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_mctx_846_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_zetaDeltaFVarIds_847_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_postponed_848_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_diag_849_);
v___x_855_ = v_reuseFailAlloc_886_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v_r_857_; 
v___x_856_ = lean_st_ref_put(v___y_817_, v___x_855_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
v_r_857_ = lean_apply_5(v_x_814_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, lean_box(0));
if (lean_obj_tag(v_r_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_874_; 
v_a_858_ = lean_ctor_get(v_r_857_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_r_857_);
if (v_isSharedCheck_874_ == 0)
{
v___x_860_ = v_r_857_;
v_isShared_861_ = v_isSharedCheck_874_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v_r_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_874_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
lean_inc(v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 1);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_873_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v___x_864_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_819_, v_isExporting_826_, v___x_841_, v___y_817_, v___x_853_, v___x_863_);
lean_dec_ref(v___x_863_);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_872_);
v___x_866_ = v___x_864_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_dec(v___x_864_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_a_858_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_858_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_875_ = lean_ctor_get(v_r_857_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v_r_857_, 1);
v___x_876_ = lean_box(0);
v___x_877_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_819_, v_isExporting_826_, v___x_841_, v___y_817_, v___x_853_, v___x_876_);
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
lean_ctor_set_tag(v___x_879_, 1);
lean_ctor_set(v___x_879_, 0, v_a_875_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_875_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_894_, lean_object* v_isExporting_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_isExporting_boxed_901_; lean_object* v_res_902_; 
v_isExporting_boxed_901_ = lean_unbox(v_isExporting_895_);
v_res_902_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_894_, v_isExporting_boxed_901_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_903_, uint8_t v_when_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
if (v_when_904_ == 0)
{
lean_object* v___x_910_; 
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_910_ = lean_apply_5(v_x_903_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
return v___x_910_;
}
else
{
uint8_t v___x_911_; lean_object* v___x_912_; 
v___x_911_ = 0;
v___x_912_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_903_, v___x_911_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_913_, lean_object* v_when_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_when_boxed_920_; lean_object* v_res_921_; 
v_when_boxed_920_ = lean_unbox(v_when_914_);
v_res_921_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_913_, v_when_boxed_920_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_922_, lean_object* v_projDecls_923_, lean_object* v___x_924_, lean_object* v___x_925_, uint8_t v_instImplicit_926_, lean_object* v___x_927_, lean_object* v_params_928_, lean_object* v_self_929_, lean_object* v_a_930_, lean_object* v___x_931_, lean_object* v_n_932_, lean_object* v___x_933_, uint8_t v_a_934_, lean_object* v_a_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_nat_dec_lt(v_a_935_, v_upperBound_922_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v_a_935_);
lean_dec(v___x_933_);
lean_dec(v_n_932_);
lean_dec_ref(v___x_931_);
lean_dec_ref(v_a_930_);
lean_dec_ref(v_self_929_);
lean_dec_ref(v_params_928_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_936_);
return v___x_943_;
}
else
{
lean_object* v___x_944_; lean_object* v_ref_945_; lean_object* v_projName_946_; lean_object* v_paramInfoOverrides_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___f_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___y_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v___x_944_ = lean_array_fget_borrowed(v_projDecls_923_, v_a_935_);
v_ref_945_ = lean_ctor_get(v___x_944_, 0);
v_projName_946_ = lean_ctor_get(v___x_944_, 1);
v_paramInfoOverrides_947_ = lean_ctor_get(v___x_944_, 2);
v___x_948_ = lean_box(v_instImplicit_926_);
v___x_949_ = lean_box(v___x_942_);
v___x_950_ = lean_box(v_a_934_);
lean_inc(v___x_933_);
lean_inc_n(v_ref_945_, 2);
lean_inc_n(v_n_932_, 2);
lean_inc(v_paramInfoOverrides_947_);
lean_inc_ref(v___x_931_);
lean_inc_ref(v_a_930_);
lean_inc_ref(v_b_936_);
lean_inc_ref(v_self_929_);
lean_inc_ref(v_params_928_);
lean_inc(v___x_927_);
lean_inc(v_a_935_);
lean_inc(v___x_925_);
lean_inc_n(v_projName_946_, 2);
lean_inc_ref(v___x_924_);
v___f_951_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_951_, 0, v___x_924_);
lean_closure_set(v___f_951_, 1, v_projName_946_);
lean_closure_set(v___f_951_, 2, v___x_925_);
lean_closure_set(v___f_951_, 3, v_a_935_);
lean_closure_set(v___f_951_, 4, v___x_948_);
lean_closure_set(v___f_951_, 5, v___x_927_);
lean_closure_set(v___f_951_, 6, v_params_928_);
lean_closure_set(v___f_951_, 7, v_self_929_);
lean_closure_set(v___f_951_, 8, v_b_936_);
lean_closure_set(v___f_951_, 9, v___x_949_);
lean_closure_set(v___f_951_, 10, v_a_930_);
lean_closure_set(v___f_951_, 11, v___x_931_);
lean_closure_set(v___f_951_, 12, v_paramInfoOverrides_947_);
lean_closure_set(v___f_951_, 13, v_n_932_);
lean_closure_set(v___f_951_, 14, v_ref_945_);
lean_closure_set(v___f_951_, 15, v___x_933_);
lean_closure_set(v___f_951_, 16, v___x_950_);
v___x_952_ = l_Lean_Expr_isForall(v_b_936_);
lean_dec_ref(v_b_936_);
v___x_953_ = lean_box(v___x_952_);
v___y_954_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_954_, 0, v___x_953_);
lean_closure_set(v___y_954_, 1, v_projName_946_);
lean_closure_set(v___y_954_, 2, v_n_932_);
lean_closure_set(v___y_954_, 3, v_ref_945_);
lean_closure_set(v___y_954_, 4, v___f_951_);
v___x_955_ = l_Lean_isPrivateName(v_projName_946_);
v___x_956_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_954_, v___x_955_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_add(v_a_935_, v___x_958_);
lean_dec(v_a_935_);
v_a_935_ = v___x_959_;
v_b_936_ = v_a_957_;
goto _start;
}
else
{
lean_dec(v_a_935_);
lean_dec(v___x_933_);
lean_dec(v_n_932_);
lean_dec_ref(v___x_931_);
lean_dec_ref(v_a_930_);
lean_dec_ref(v_self_929_);
lean_dec_ref(v_params_928_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_961_ = _args[0];
lean_object* v_projDecls_962_ = _args[1];
lean_object* v___x_963_ = _args[2];
lean_object* v___x_964_ = _args[3];
lean_object* v_instImplicit_965_ = _args[4];
lean_object* v___x_966_ = _args[5];
lean_object* v_params_967_ = _args[6];
lean_object* v_self_968_ = _args[7];
lean_object* v_a_969_ = _args[8];
lean_object* v___x_970_ = _args[9];
lean_object* v_n_971_ = _args[10];
lean_object* v___x_972_ = _args[11];
lean_object* v_a_973_ = _args[12];
lean_object* v_a_974_ = _args[13];
lean_object* v_b_975_ = _args[14];
lean_object* v___y_976_ = _args[15];
lean_object* v___y_977_ = _args[16];
lean_object* v___y_978_ = _args[17];
lean_object* v___y_979_ = _args[18];
lean_object* v___y_980_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_981_; uint8_t v_a_17748__boxed_982_; lean_object* v_res_983_; 
v_instImplicit_boxed_981_ = lean_unbox(v_instImplicit_965_);
v_a_17748__boxed_982_ = lean_unbox(v_a_973_);
v_res_983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_961_, v_projDecls_962_, v___x_963_, v___x_964_, v_instImplicit_boxed_981_, v___x_966_, v_params_967_, v_self_968_, v_a_969_, v___x_970_, v_n_971_, v___x_972_, v_a_17748__boxed_982_, v_a_974_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_projDecls_962_);
lean_dec(v_upperBound_961_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_984_, lean_object* v_as_985_, size_t v_sz_986_, size_t v_i_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_987_, v_sz_986_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_b_988_);
return v___x_994_;
}
else
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_a_995_ = lean_array_uget_borrowed(v_as_985_, v_i_987_);
v___x_996_ = l_Lean_Expr_fvarId_x21(v_a_995_);
lean_inc(v___x_996_);
v___x_997_ = l_Lean_FVarId_getDecl___redArg(v___x_996_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v_a_1000_; uint8_t v___y_1005_; uint8_t v___x_1008_; uint8_t v___x_1009_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_1008_ = l_Lean_LocalDecl_binderInfo(v_a_998_);
v___x_1009_ = l_Lean_BinderInfo_isInstImplicit(v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = l_Lean_LocalDecl_type(v_a_998_);
lean_dec(v_a_998_);
v___x_1012_ = l_Lean_Expr_isOutParam(v___x_1011_);
lean_dec_ref(v___x_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = 0;
v___x_1014_ = l_Lean_LocalContext_setBinderInfo(v_b_988_, v___x_996_, v___x_1013_);
v_a_1000_ = v___x_1014_;
goto v___jp_999_;
}
else
{
goto v___jp_1010_;
}
}
else
{
lean_dec(v_a_998_);
goto v___jp_1010_;
}
v___jp_999_:
{
size_t v___x_1001_; size_t v___x_1002_; 
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_987_, v___x_1001_);
v_i_987_ = v___x_1002_;
v_b_988_ = v_a_1000_;
goto _start;
}
v___jp_1004_:
{
if (v___y_1005_ == 0)
{
lean_dec(v___x_996_);
v_a_1000_ = v_b_988_;
goto v___jp_999_;
}
else
{
uint8_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = 1;
v___x_1007_ = l_Lean_LocalContext_setBinderInfo(v_b_988_, v___x_996_, v___x_1006_);
v_a_1000_ = v___x_1007_;
goto v___jp_999_;
}
}
v___jp_1010_:
{
if (v___x_1009_ == 0)
{
v___y_1005_ = v___x_1009_;
goto v___jp_1004_;
}
else
{
v___y_1005_ = v_instImplicit_984_;
goto v___jp_1004_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v___x_996_);
lean_dec_ref(v_b_988_);
v_a_1015_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_997_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_997_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
uint8_t v_instImplicit_boxed_1032_; size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_instImplicit_boxed_1032_ = lean_unbox(v_instImplicit_1023_);
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1032_, v_as_1024_, v_sz_boxed_1033_, v_i_boxed_1034_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec_ref(v_as_1024_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1036_, uint8_t v_instImplicit_1037_, lean_object* v_projDecls_1038_, lean_object* v_toConstantVal_1039_, lean_object* v_numParams_1040_, lean_object* v___x_1041_, lean_object* v_n_1042_, lean_object* v_levelParams_1043_, uint8_t v_a_1044_, lean_object* v_ctorType_1045_, lean_object* v_self_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_lctx_1052_; lean_object* v___x_1053_; size_t v_sz_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v_lctx_1052_ = lean_ctor_get(v___y_1047_, 2);
lean_inc_ref(v_self_1046_);
lean_inc_ref(v_params_1036_);
v___x_1053_ = lean_array_push(v_params_1036_, v_self_1046_);
v_sz_1054_ = lean_array_size(v_params_1036_);
v___x_1055_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1052_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1037_, v_params_1036_, v_sz_1054_, v___x_1055_, v_lctx_1052_, v___y_1047_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = lean_array_get_size(v_projDecls_1038_);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1058_, v_projDecls_1038_, v_toConstantVal_1039_, v_numParams_1040_, v_instImplicit_1037_, v___x_1041_, v_params_1036_, v_self_1046_, v_a_1057_, v___x_1053_, v_n_1042_, v_levelParams_1043_, v_a_1044_, v___x_1059_, v_ctorType_1045_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v___x_1060_, 0);
lean_dec(v_unused_1069_);
v___x_1062_ = v___x_1060_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v___x_1060_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_box(0);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1060_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1060_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v___x_1053_);
lean_dec_ref(v_self_1046_);
lean_dec_ref(v_ctorType_1045_);
lean_dec(v_levelParams_1043_);
lean_dec(v_n_1042_);
lean_dec(v___x_1041_);
lean_dec(v_numParams_1040_);
lean_dec_ref(v_toConstantVal_1039_);
lean_dec_ref(v_params_1036_);
v_a_1078_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1056_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1056_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1086_, lean_object* v_instImplicit_1087_, lean_object* v_projDecls_1088_, lean_object* v_toConstantVal_1089_, lean_object* v_numParams_1090_, lean_object* v___x_1091_, lean_object* v_n_1092_, lean_object* v_levelParams_1093_, lean_object* v_a_1094_, lean_object* v_ctorType_1095_, lean_object* v_self_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_instImplicit_boxed_1102_; uint8_t v_a_17890__boxed_1103_; lean_object* v_res_1104_; 
v_instImplicit_boxed_1102_ = lean_unbox(v_instImplicit_1087_);
v_a_17890__boxed_1103_ = lean_unbox(v_a_1094_);
v_res_1104_ = l_Lean_Meta_mkProjections___lam__0(v_params_1086_, v_instImplicit_boxed_1102_, v_projDecls_1088_, v_toConstantVal_1089_, v_numParams_1090_, v___x_1091_, v_n_1092_, v_levelParams_1093_, v_a_17890__boxed_1103_, v_ctorType_1095_, v_self_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec_ref(v_projDecls_1088_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1114_, lean_object* v_projDecls_1115_, lean_object* v_toConstantVal_1116_, lean_object* v_numParams_1117_, lean_object* v___x_1118_, lean_object* v_n_1119_, lean_object* v_levelParams_1120_, uint8_t v_a_1121_, lean_object* v_params_1122_, lean_object* v_ctorType_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; uint8_t v___y_1136_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1140_ = lean_box(v_instImplicit_1114_);
v___x_1141_ = lean_box(v_a_1121_);
lean_inc(v_n_1119_);
lean_inc(v___x_1118_);
lean_inc(v_numParams_1117_);
lean_inc_ref(v_params_1122_);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1142_, 0, v_params_1122_);
lean_closure_set(v___f_1142_, 1, v___x_1140_);
lean_closure_set(v___f_1142_, 2, v_projDecls_1115_);
lean_closure_set(v___f_1142_, 3, v_toConstantVal_1116_);
lean_closure_set(v___f_1142_, 4, v_numParams_1117_);
lean_closure_set(v___f_1142_, 5, v___x_1118_);
lean_closure_set(v___f_1142_, 6, v_n_1119_);
lean_closure_set(v___f_1142_, 7, v_levelParams_1120_);
lean_closure_set(v___f_1142_, 8, v___x_1141_);
lean_closure_set(v___f_1142_, 9, v_ctorType_1123_);
v___x_1148_ = lean_array_get_size(v_params_1122_);
v___x_1149_ = lean_nat_dec_eq(v___x_1148_, v_numParams_1117_);
lean_dec(v_numParams_1117_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v___f_1142_);
lean_dec_ref(v_params_1122_);
lean_dec(v___x_1118_);
v___x_1150_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1151_ = l_Lean_MessageData_ofConstName(v_n_1119_, v___x_1149_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1154_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1155_;
}
else
{
goto v___jp_1143_;
}
v___jp_1129_:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1138_ = 0;
v___x_1139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1137_, v___y_1136_, v___y_1132_, v___y_1133_, v___x_1138_, v___y_1131_, v___y_1135_, v___y_1130_, v___y_1134_);
return v___x_1139_;
}
v___jp_1143_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = l_Lean_Expr_const___override(v_n_1119_, v___x_1118_);
v___x_1145_ = l_Lean_mkAppN(v___x_1144_, v_params_1122_);
lean_dec_ref(v_params_1122_);
if (v_instImplicit_1114_ == 0)
{
uint8_t v___x_1146_; 
v___x_1146_ = 0;
v___y_1130_ = v___y_1126_;
v___y_1131_ = v___y_1124_;
v___y_1132_ = v___x_1145_;
v___y_1133_ = v___f_1142_;
v___y_1134_ = v___y_1127_;
v___y_1135_ = v___y_1125_;
v___y_1136_ = v___x_1146_;
goto v___jp_1129_;
}
else
{
uint8_t v___x_1147_; 
v___x_1147_ = 3;
v___y_1130_ = v___y_1126_;
v___y_1131_ = v___y_1124_;
v___y_1132_ = v___x_1145_;
v___y_1133_ = v___f_1142_;
v___y_1134_ = v___y_1127_;
v___y_1135_ = v___y_1125_;
v___y_1136_ = v___x_1147_;
goto v___jp_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1156_, lean_object* v_projDecls_1157_, lean_object* v_toConstantVal_1158_, lean_object* v_numParams_1159_, lean_object* v___x_1160_, lean_object* v_n_1161_, lean_object* v_levelParams_1162_, lean_object* v_a_1163_, lean_object* v_params_1164_, lean_object* v_ctorType_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_instImplicit_boxed_1171_; uint8_t v_a_17994__boxed_1172_; lean_object* v_res_1173_; 
v_instImplicit_boxed_1171_ = lean_unbox(v_instImplicit_1156_);
v_a_17994__boxed_1172_ = lean_unbox(v_a_1163_);
v_res_1173_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1171_, v_projDecls_1157_, v_toConstantVal_1158_, v_numParams_1159_, v___x_1160_, v_n_1161_, v_levelParams_1162_, v_a_17994__boxed_1172_, v_params_1164_, v_ctorType_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
if (lean_obj_tag(v_a_1174_) == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = l_List_reverse___redArg(v_a_1175_);
return v___x_1176_;
}
else
{
lean_object* v_head_1177_; lean_object* v_tail_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1187_; 
v_head_1177_ = lean_ctor_get(v_a_1174_, 0);
v_tail_1178_ = lean_ctor_get(v_a_1174_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_a_1174_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1180_ = v_a_1174_;
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_tail_1178_);
lean_inc(v_head_1177_);
lean_dec(v_a_1174_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_mkLevelParam(v_head_1177_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v_a_1175_);
lean_ctor_set(v___x_1180_, 0, v___x_1182_);
v___x_1184_ = v___x_1180_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_a_1175_);
v___x_1184_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v_a_1174_ = v_tail_1178_;
v_a_1175_ = v___x_1184_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_instMonadEIO(lean_box(0));
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_toApplicative_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1262_; 
v___x_1199_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1200_ = l_StateRefT_x27_instMonad___redArg(v___x_1199_);
v_toApplicative_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1200_, 1);
lean_dec(v_unused_1263_);
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1262_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_toApplicative_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1262_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_toFunctor_1205_; lean_object* v_toSeq_1206_; lean_object* v_toSeqLeft_1207_; lean_object* v_toSeqRight_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1260_; 
v_toFunctor_1205_ = lean_ctor_get(v_toApplicative_1201_, 0);
v_toSeq_1206_ = lean_ctor_get(v_toApplicative_1201_, 2);
v_toSeqLeft_1207_ = lean_ctor_get(v_toApplicative_1201_, 3);
v_toSeqRight_1208_ = lean_ctor_get(v_toApplicative_1201_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_toApplicative_1201_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_toApplicative_1201_, 1);
lean_dec(v_unused_1261_);
v___x_1210_ = v_toApplicative_1201_;
v_isShared_1211_ = v_isSharedCheck_1260_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_toSeqRight_1208_);
lean_inc(v_toSeqLeft_1207_);
lean_inc(v_toSeq_1206_);
lean_inc(v_toFunctor_1205_);
lean_dec(v_toApplicative_1201_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1260_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___f_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1221_; 
v___f_1212_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1213_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1205_);
v___f_1214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1214_, 0, v_toFunctor_1205_);
v___f_1215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1215_, 0, v_toFunctor_1205_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___f_1214_);
lean_ctor_set(v___x_1216_, 1, v___f_1215_);
v___f_1217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1217_, 0, v_toSeqRight_1208_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toSeqLeft_1207_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toSeq_1206_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 4, v___f_1217_);
lean_ctor_set(v___x_1210_, 3, v___f_1218_);
lean_ctor_set(v___x_1210_, 2, v___f_1219_);
lean_ctor_set(v___x_1210_, 1, v___f_1212_);
lean_ctor_set(v___x_1210_, 0, v___x_1216_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___f_1212_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v___f_1219_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___f_1218_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___f_1217_);
v___x_1221_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___f_1213_);
lean_ctor_set(v___x_1203_, 0, v___x_1221_);
v___x_1223_ = v___x_1203_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___f_1213_);
v___x_1223_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v_toApplicative_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1256_; 
v___x_1224_ = l_StateRefT_x27_instMonad___redArg(v___x_1223_);
v_toApplicative_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1224_, 1);
lean_dec(v_unused_1257_);
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_toApplicative_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1256_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_toFunctor_1229_; lean_object* v_toSeq_1230_; lean_object* v_toSeqLeft_1231_; lean_object* v_toSeqRight_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1254_; 
v_toFunctor_1229_ = lean_ctor_get(v_toApplicative_1225_, 0);
v_toSeq_1230_ = lean_ctor_get(v_toApplicative_1225_, 2);
v_toSeqLeft_1231_ = lean_ctor_get(v_toApplicative_1225_, 3);
v_toSeqRight_1232_ = lean_ctor_get(v_toApplicative_1225_, 4);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_toApplicative_1225_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_dec(v_unused_1255_);
v___x_1234_ = v_toApplicative_1225_;
v_isShared_1235_ = v_isSharedCheck_1254_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_toSeqRight_1232_);
lean_inc(v_toSeqLeft_1231_);
lean_inc(v_toSeq_1230_);
lean_inc(v_toFunctor_1229_);
lean_dec(v_toApplicative_1225_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1254_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___x_1245_; 
v___f_1236_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1237_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1229_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toFunctor_1229_);
v___f_1239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1239_, 0, v_toFunctor_1229_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___f_1238_);
lean_ctor_set(v___x_1240_, 1, v___f_1239_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeqRight_1232_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toSeqLeft_1231_);
v___f_1243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1243_, 0, v_toSeq_1230_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v___f_1241_);
lean_ctor_set(v___x_1234_, 3, v___f_1242_);
lean_ctor_set(v___x_1234_, 2, v___f_1243_);
lean_ctor_set(v___x_1234_, 1, v___f_1236_);
lean_ctor_set(v___x_1234_, 0, v___x_1240_);
v___x_1245_ = v___x_1234_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___f_1236_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v___f_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v___f_1241_);
v___x_1245_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v___f_1237_);
lean_ctor_set(v___x_1227_, 0, v___x_1245_);
v___x_1247_ = v___x_1227_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___f_1237_);
v___x_1247_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_13036__overap_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_instInhabitedOfMonad___redArg(v___x_1247_, v___x_1248_);
v___x_13036__overap_1250_ = lean_panic_fn_borrowed(v___x_1249_, v_msg_1193_);
lean_dec(v___x_1249_);
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
lean_inc(v___y_1195_);
lean_inc_ref(v___y_1194_);
v___x_1251_ = lean_apply_5(v___x_13036__overap_1250_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, lean_box(0));
return v___x_1251_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1278_ = lean_unsigned_to_nat(11u);
v___x_1279_ = lean_unsigned_to_nat(122u);
v___x_1280_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1281_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1282_ = l_mkPanicMessageWithDecl(v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_, v___x_1277_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1297_; lean_object* v_env_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_st_ref_get(v___y_1287_);
v_env_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref(v_env_1298_);
lean_dec(v___x_1297_);
v___x_1299_ = 0;
lean_inc(v_constName_1283_);
v___x_1300_ = l_Lean_Environment_findAsync_x3f(v_env_1298_, v_constName_1283_, v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 1)
{
lean_object* v_val_1301_; uint8_t v_kind_1302_; 
v_val_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_kind_1302_ = lean_ctor_get_uint8(v_val_1301_, sizeof(void*)*3);
if (v_kind_1302_ == 6)
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1301_);
if (lean_obj_tag(v___x_1303_) == 6)
{
lean_object* v_val_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_constName_1283_);
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_val_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 0);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_val_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1303_);
v___x_1312_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1313_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1312_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
if (lean_obj_tag(v_a_1314_) == 0)
{
lean_del_object(v___x_1316_);
goto v___jp_1289_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1320_; 
lean_dec(v_constName_1283_);
v_val_1318_ = lean_ctor_get(v_a_1314_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v_a_1314_, 1);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_val_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_val_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_constName_1283_);
v_a_1323_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1313_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1313_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_dec(v_val_1301_);
goto v___jp_1289_;
}
}
else
{
lean_dec(v___x_1300_);
goto v___jp_1289_;
}
v___jp_1289_:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1290_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1291_ = 0;
v___x_1292_ = l_Lean_MessageData_ofConstName(v_constName_1283_, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1290_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1295_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1337_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_env_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_st_ref_get(v___y_1345_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1347_);
lean_inc(v_constName_1341_);
v___x_1349_ = l_Lean_isInductiveCore_x3f(v_env_1348_, v_constName_1341_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1351_ = 0;
v___x_1352_ = l_Lean_MessageData_ofConstName(v_constName_1341_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1350_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1355_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_constName_1341_);
v_val_1357_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1349_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_val_1357_);
lean_dec(v___x_1349_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 0);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_val_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1378_, lean_object* v___x_1379_, uint8_t v_instImplicit_1380_, lean_object* v_projDecls_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
lean_inc(v_n_1378_);
v___x_1387_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1378_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1429_ = l_Lean_InductiveVal_numCtors(v_a_1388_);
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_dec_eq(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_a_1388_);
lean_dec_ref(v_projDecls_1381_);
v___x_1432_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1433_ = l_Lean_MessageData_ofConstName(v_n_1378_, v___x_1431_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1436_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1437_;
}
else
{
v___y_1390_ = v___y_1382_;
v___y_1391_ = v___y_1383_;
v___y_1392_ = v___y_1384_;
v___y_1393_ = v___y_1385_;
goto v___jp_1389_;
}
v___jp_1389_:
{
lean_object* v_toConstantVal_1394_; lean_object* v_numParams_1395_; lean_object* v_ctors_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_toConstantVal_1394_ = lean_ctor_get(v_a_1388_, 0);
lean_inc_ref(v_toConstantVal_1394_);
v_numParams_1395_ = lean_ctor_get(v_a_1388_, 1);
lean_inc(v_numParams_1395_);
v_ctors_1396_ = lean_ctor_get(v_a_1388_, 4);
lean_inc(v_ctors_1396_);
lean_dec(v_a_1388_);
v___x_1397_ = l_List_head_x21___redArg(v___x_1379_, v_ctors_1396_);
lean_dec(v_ctors_1396_);
v___x_1398_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1397_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v_levelParams_1400_; lean_object* v_type_1401_; lean_object* v___x_1402_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref_known(v___x_1398_, 1);
v_levelParams_1400_ = lean_ctor_get(v_toConstantVal_1394_, 1);
lean_inc(v_levelParams_1400_);
v_type_1401_ = lean_ctor_get(v_toConstantVal_1394_, 2);
lean_inc_ref(v_type_1401_);
lean_dec_ref(v_toConstantVal_1394_);
v___x_1402_ = l_Lean_Meta_isPropFormerType(v_type_1401_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_toConstantVal_1403_; lean_object* v_a_1404_; lean_object* v_type_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_toConstantVal_1403_ = lean_ctor_get(v_a_1399_, 0);
lean_inc_ref(v_toConstantVal_1403_);
lean_dec(v_a_1399_);
v_a_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1402_, 1);
v_type_1405_ = lean_ctor_get(v_toConstantVal_1403_, 2);
lean_inc_ref(v_type_1405_);
v___x_1406_ = lean_box(0);
lean_inc(v_levelParams_1400_);
v___x_1407_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1400_, v___x_1406_);
v___x_1408_ = lean_box(v_instImplicit_1380_);
lean_inc(v_numParams_1395_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1409_, 0, v___x_1408_);
lean_closure_set(v___f_1409_, 1, v_projDecls_1381_);
lean_closure_set(v___f_1409_, 2, v_toConstantVal_1403_);
lean_closure_set(v___f_1409_, 3, v_numParams_1395_);
lean_closure_set(v___f_1409_, 4, v___x_1407_);
lean_closure_set(v___f_1409_, 5, v_n_1378_);
lean_closure_set(v___f_1409_, 6, v_levelParams_1400_);
lean_closure_set(v___f_1409_, 7, v_a_1404_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_numParams_1395_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1405_, v___x_1410_, v___f_1409_, v___x_1411_, v___x_1411_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
return v___x_1412_;
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_levelParams_1400_);
lean_dec(v_a_1399_);
lean_dec(v_numParams_1395_);
lean_dec_ref(v_projDecls_1381_);
lean_dec(v_n_1378_);
v_a_1413_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1402_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1402_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_numParams_1395_);
lean_dec_ref(v_toConstantVal_1394_);
lean_dec_ref(v_projDecls_1381_);
lean_dec(v_n_1378_);
v_a_1421_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1398_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1398_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v_projDecls_1381_);
lean_dec(v_n_1378_);
v_a_1438_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1387_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1387_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1446_, lean_object* v___x_1447_, lean_object* v_instImplicit_1448_, lean_object* v_projDecls_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v_instImplicit_boxed_1455_; lean_object* v_res_1456_; 
v_instImplicit_boxed_1455_ = lean_unbox(v_instImplicit_1448_);
v_res_1456_ = l_Lean_Meta_mkProjections___lam__2(v_n_1446_, v___x_1447_, v_instImplicit_boxed_1455_, v_projDecls_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___x_1447_);
return v_res_1456_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_unsigned_to_nat(32u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = ((size_t)5ULL);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_unsigned_to_nat(32u);
v___x_1466_ = lean_mk_empty_array_with_capacity(v___x_1465_);
v___x_1467_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1468_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
lean_ctor_set(v___x_1468_, 2, v___x_1464_);
lean_ctor_set(v___x_1468_, 3, v___x_1464_);
lean_ctor_set_usize(v___x_1468_, 4, v___x_1463_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1469_ = lean_box(1);
v___x_1470_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1471_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1470_);
lean_ctor_set(v___x_1472_, 2, v___x_1469_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1475_, lean_object* v_projDecls_1476_, uint8_t v_instImplicit_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_box(v_instImplicit_1477_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1485_, 0, v_n_1475_);
lean_closure_set(v___f_1485_, 1, v___x_1483_);
lean_closure_set(v___f_1485_, 2, v___x_1484_);
lean_closure_set(v___f_1485_, 3, v_projDecls_1476_);
v___x_1486_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1487_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1488_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1486_, v___x_1487_, v___f_1485_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1489_, lean_object* v_projDecls_1490_, lean_object* v_instImplicit_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
uint8_t v_instImplicit_boxed_1497_; lean_object* v_res_1498_; 
v_instImplicit_boxed_1497_ = lean_unbox(v_instImplicit_1491_);
v_res_1498_ = l_Lean_Meta_mkProjections(v_n_1489_, v_projDecls_1490_, v_instImplicit_boxed_1497_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1499_, lean_object* v_as_1500_, size_t v_sz_1501_, size_t v_i_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1499_, v_as_1500_, v_sz_1501_, v_i_1502_, v_b_1503_, v___y_1504_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1510_, lean_object* v_as_1511_, lean_object* v_sz_1512_, lean_object* v_i_1513_, lean_object* v_b_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
uint8_t v_instImplicit_boxed_1520_; size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v_instImplicit_boxed_1520_ = lean_unbox(v_instImplicit_1510_);
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1512_);
lean_dec(v_sz_1512_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1520_, v_as_1511_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec_ref(v_as_1511_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1524_, uint8_t v_s_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1524_, v_s_1525_, v___y_1527_, v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1532_, lean_object* v_s_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_s_boxed_1539_; lean_object* v_res_1540_; 
v_s_boxed_1539_ = lean_unbox(v_s_1533_);
v_res_1540_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1532_, v_s_boxed_1539_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1541_, lean_object* v_ref_1542_, lean_object* v_msg_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1542_, v_msg_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_ref_1551_, lean_object* v_msg_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1550_, v_ref_1551_, v_msg_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_ref_1551_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1559_, lean_object* v_x_1560_, uint8_t v_isExporting_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1560_, v_isExporting_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_x_1569_, lean_object* v_isExporting_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_isExporting_boxed_1576_; lean_object* v_res_1577_; 
v_isExporting_boxed_1576_ = lean_unbox(v_isExporting_1570_);
v_res_1577_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1568_, v_x_1569_, v_isExporting_boxed_1576_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1578_, lean_object* v_x_1579_, uint8_t v_when_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1579_, v_when_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1587_, lean_object* v_x_1588_, lean_object* v_when_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_when_boxed_1595_; lean_object* v_res_1596_; 
v_when_boxed_1595_ = lean_unbox(v_when_1589_);
v_res_1596_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1587_, v_x_1588_, v_when_boxed_1595_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1597_, lean_object* v_projDecls_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, uint8_t v_instImplicit_1601_, lean_object* v___x_1602_, lean_object* v_params_1603_, lean_object* v_self_1604_, lean_object* v_a_1605_, lean_object* v___x_1606_, lean_object* v_n_1607_, lean_object* v___x_1608_, uint8_t v_a_1609_, lean_object* v_inst_1610_, lean_object* v_R_1611_, lean_object* v_a_1612_, lean_object* v_b_1613_, lean_object* v_c_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1597_, v_projDecls_1598_, v___x_1599_, v___x_1600_, v_instImplicit_1601_, v___x_1602_, v_params_1603_, v_self_1604_, v_a_1605_, v___x_1606_, v_n_1607_, v___x_1608_, v_a_1609_, v_a_1612_, v_b_1613_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1621_ = _args[0];
lean_object* v_projDecls_1622_ = _args[1];
lean_object* v___x_1623_ = _args[2];
lean_object* v___x_1624_ = _args[3];
lean_object* v_instImplicit_1625_ = _args[4];
lean_object* v___x_1626_ = _args[5];
lean_object* v_params_1627_ = _args[6];
lean_object* v_self_1628_ = _args[7];
lean_object* v_a_1629_ = _args[8];
lean_object* v___x_1630_ = _args[9];
lean_object* v_n_1631_ = _args[10];
lean_object* v___x_1632_ = _args[11];
lean_object* v_a_1633_ = _args[12];
lean_object* v_inst_1634_ = _args[13];
lean_object* v_R_1635_ = _args[14];
lean_object* v_a_1636_ = _args[15];
lean_object* v_b_1637_ = _args[16];
lean_object* v_c_1638_ = _args[17];
lean_object* v___y_1639_ = _args[18];
lean_object* v___y_1640_ = _args[19];
lean_object* v___y_1641_ = _args[20];
lean_object* v___y_1642_ = _args[21];
lean_object* v___y_1643_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1644_; uint8_t v_a_18747__boxed_1645_; lean_object* v_res_1646_; 
v_instImplicit_boxed_1644_ = lean_unbox(v_instImplicit_1625_);
v_a_18747__boxed_1645_ = lean_unbox(v_a_1633_);
v_res_1646_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1621_, v_projDecls_1622_, v___x_1623_, v___x_1624_, v_instImplicit_boxed_1644_, v___x_1626_, v_params_1627_, v_self_1628_, v_a_1629_, v___x_1630_, v_n_1631_, v___x_1632_, v_a_18747__boxed_1645_, v_inst_1634_, v_R_1635_, v_a_1636_, v_b_1637_, v_c_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v_projDecls_1622_);
lean_dec(v_upperBound_1621_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1647_, uint8_t v_allowLevelAssignments_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1648_, v_k_1647_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1654_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1654_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1671_, lean_object* v_allowLevelAssignments_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1678_; lean_object* v_res_1679_; 
v_allowLevelAssignments_boxed_1678_ = lean_unbox(v_allowLevelAssignments_1672_);
v_res_1679_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1671_, v_allowLevelAssignments_boxed_1678_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1680_, lean_object* v_k_1681_, uint8_t v_allowLevelAssignments_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1681_, v_allowLevelAssignments_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1689_, lean_object* v_k_1690_, lean_object* v_allowLevelAssignments_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1697_; lean_object* v_res_1698_; 
v_allowLevelAssignments_boxed_1697_ = lean_unbox(v_allowLevelAssignments_1691_);
v_res_1698_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1689_, v_k_1690_, v_allowLevelAssignments_boxed_1697_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_b_1702_);
return v___x_1709_;
}
else
{
lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1765_; 
v_snd_1710_ = lean_ctor_get(v_b_1702_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_b_1702_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v_b_1702_, 0);
lean_dec(v_unused_1766_);
v___x_1712_ = v_b_1702_;
v_isShared_1713_ = v_isSharedCheck_1765_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_dec(v_b_1702_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1765_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_array_1714_; lean_object* v_start_1715_; lean_object* v_stop_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_array_1714_ = lean_ctor_get(v_snd_1710_, 0);
v_start_1715_ = lean_ctor_get(v_snd_1710_, 1);
v_stop_1716_ = lean_ctor_get(v_snd_1710_, 2);
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_nat_dec_lt(v_start_1715_, v_stop_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1720_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1717_);
v___x_1720_ = v___x_1712_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_snd_1710_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
else
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1761_; 
lean_inc(v_stop_1716_);
lean_inc(v_start_1715_);
lean_inc_ref(v_array_1714_);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_snd_1710_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1762_ = lean_ctor_get(v_snd_1710_, 2);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_snd_1710_, 1);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_snd_1710_, 0);
lean_dec(v_unused_1764_);
v___x_1724_ = v_snd_1710_;
v_isShared_1725_ = v_isSharedCheck_1761_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_snd_1710_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1761_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
v___x_1727_ = lean_array_fget_borrowed(v_array_1714_, v_start_1715_);
lean_inc(v___x_1727_);
lean_inc(v_a_1726_);
v___x_1728_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1726_, v___x_1727_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1752_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1752_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1752_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_start_1715_, v___x_1733_);
lean_dec(v_start_1715_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1734_);
v___x_1736_ = v___x_1724_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_array_1714_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_stop_1716_);
v___x_1736_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_unbox(v_a_1729_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1729_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1736_);
lean_ctor_set(v___x_1712_, 0, v___x_1738_);
v___x_1740_ = v___x_1712_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1736_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1740_);
v___x_1742_ = v___x_1731_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
else
{
lean_object* v___x_1746_; 
lean_del_object(v___x_1731_);
lean_dec(v_a_1729_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1736_);
lean_ctor_set(v___x_1712_, 0, v___x_1717_);
v___x_1746_ = v___x_1712_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1736_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
size_t v___x_1747_; size_t v___x_1748_; 
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1701_, v___x_1747_);
v_i_1701_ = v___x_1748_;
v_b_1702_ = v___x_1746_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_del_object(v___x_1724_);
lean_dec(v_stop_1716_);
lean_dec(v_start_1715_);
lean_dec_ref(v_array_1714_);
lean_del_object(v___x_1712_);
v_a_1753_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1728_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1728_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1767_, lean_object* v_sz_1768_, lean_object* v_i_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
size_t v_sz_boxed_1776_; size_t v_i_boxed_1777_; lean_object* v_res_1778_; 
v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1768_);
lean_dec(v_sz_1768_);
v_i_boxed_1777_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1767_, v_sz_boxed_1776_, v_i_boxed_1777_, v_b_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v_as_1767_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1779_, lean_object* v_params2_1780_, lean_object* v___x_1781_, lean_object* v_params1_1782_, uint8_t v___x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
if (v___x_1779_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v___x_1781_);
lean_dec_ref(v_params2_1780_);
v___x_1789_ = lean_box(v___x_1779_);
v___x_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; size_t v_sz_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = l_Array_toSubarray___redArg(v_params2_1780_, v___x_1791_, v___x_1781_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___x_1792_);
v_sz_1795_ = lean_array_size(v_params1_1782_);
v___x_1796_ = ((size_t)0ULL);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1782_, v_sz_1795_, v___x_1796_, v___x_1794_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1811_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1811_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1811_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_fst_1802_; 
v_fst_1802_ = lean_ctor_get(v_a_1798_, 0);
lean_inc(v_fst_1802_);
lean_dec(v_a_1798_);
if (lean_obj_tag(v_fst_1802_) == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_box(v___x_1783_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v_val_1807_; lean_object* v___x_1809_; 
v_val_1807_ = lean_ctor_get(v_fst_1802_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v_fst_1802_, 1);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v_val_1807_);
v___x_1809_ = v___x_1800_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_val_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1797_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1797_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1820_, lean_object* v_params2_1821_, lean_object* v___x_1822_, lean_object* v_params1_1823_, lean_object* v___x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___x_2006__boxed_1830_; uint8_t v___x_2008__boxed_1831_; lean_object* v_res_1832_; 
v___x_2006__boxed_1830_ = lean_unbox(v___x_1820_);
v___x_2008__boxed_1831_ = lean_unbox(v___x_1824_);
v_res_1832_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2006__boxed_1830_, v_params2_1821_, v___x_1822_, v_params1_1823_, v___x_2008__boxed_1831_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_params1_1823_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1833_, lean_object* v_params2_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___y_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1840_ = lean_array_get_size(v_params1_1833_);
v___x_1841_ = lean_array_get_size(v_params2_1834_);
v___x_1842_ = lean_nat_dec_eq(v___x_1840_, v___x_1841_);
v___x_1843_ = 1;
v___x_1844_ = lean_box(v___x_1842_);
v___x_1845_ = lean_box(v___x_1843_);
v___y_1846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1846_, 0, v___x_1844_);
lean_closure_set(v___y_1846_, 1, v_params2_1834_);
lean_closure_set(v___y_1846_, 2, v___x_1841_);
lean_closure_set(v___y_1846_, 3, v_params1_1833_);
lean_closure_set(v___y_1846_, 4, v___x_1845_);
v___x_1847_ = 0;
v___x_1848_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1846_, v___x_1847_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1849_, lean_object* v_params2_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1849_, v_params2_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v_env_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = lean_st_ref_get(v___y_1858_);
v_env_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_env_1861_);
lean_dec(v___x_1860_);
v___x_1862_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1861_, v_declName_1857_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1864_, v___y_1865_);
lean_dec(v___y_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1868_, v___y_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1882_; lean_object* v_dummy_1883_; 
v___x_1882_ = lean_box(0);
v_dummy_1883_ = l_Lean_Expr_sort___override(v___x_1882_);
return v_dummy_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1884_, lean_object* v_induct_1885_, lean_object* v_params_1886_, lean_object* v_idx_1887_, lean_object* v_e_1888_, lean_object* v_x_x3f_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
if (lean_obj_tag(v_e_1888_) == 11)
{
lean_object* v_typeName_1901_; lean_object* v_idx_1902_; lean_object* v_struct_1903_; uint8_t v___x_1950_; 
v_typeName_1901_ = lean_ctor_get(v_e_1888_, 0);
v_idx_1902_ = lean_ctor_get(v_e_1888_, 1);
v_struct_1903_ = lean_ctor_get(v_e_1888_, 2);
lean_inc_ref(v_struct_1903_);
v___x_1950_ = lean_nat_dec_eq(v_idx_1902_, v_idx_1887_);
if (v___x_1950_ == 0)
{
lean_dec_ref(v_struct_1903_);
lean_dec_ref_known(v_e_1888_, 3);
lean_dec_ref(v_params_1886_);
goto v___jp_1895_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_name_eq(v_induct_1885_, v_typeName_1901_);
if (v___x_1951_ == 0)
{
lean_dec_ref(v_struct_1903_);
lean_dec_ref_known(v_e_1888_, 3);
lean_dec_ref(v_params_1886_);
goto v___jp_1895_;
}
else
{
if (lean_obj_tag(v_x_x3f_1889_) == 0)
{
goto v___jp_1904_;
}
else
{
lean_object* v_val_1952_; uint8_t v___x_1953_; 
v_val_1952_ = lean_ctor_get(v_x_x3f_1889_, 0);
v___x_1953_ = lean_expr_eqv(v_val_1952_, v_struct_1903_);
if (v___x_1953_ == 0)
{
lean_dec_ref(v_struct_1903_);
lean_dec_ref_known(v_e_1888_, 3);
lean_dec_ref(v_params_1886_);
goto v___jp_1895_;
}
else
{
goto v___jp_1904_;
}
}
}
}
v___jp_1904_:
{
lean_object* v___x_1905_; 
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
lean_inc(v_a_1891_);
lean_inc_ref(v_a_1890_);
v___x_1905_ = lean_infer_type(v_e_1888_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
lean_inc(v_a_1891_);
lean_inc_ref(v_a_1890_);
v___x_1907_ = lean_whnf(v_a_1906_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v_dummy_1909_; lean_object* v_nargs_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_dummy_1909_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1910_ = l_Lean_Expr_getAppNumArgs(v_a_1908_);
lean_inc(v_nargs_1910_);
v___x_1911_ = lean_mk_array(v_nargs_1910_, v_dummy_1909_);
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_sub(v_nargs_1910_, v___x_1912_);
lean_dec(v_nargs_1910_);
v___x_1914_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1908_, v___x_1911_, v___x_1913_);
v___x_1915_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1886_, v___x_1914_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1925_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1925_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1925_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
if (v___x_1920_ == 0)
{
lean_del_object(v___x_1918_);
lean_dec_ref(v_struct_1903_);
goto v___jp_1895_;
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_struct_1903_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_struct_1903_);
v_a_1926_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1915_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1915_);
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
lean_dec_ref(v_struct_1903_);
lean_dec_ref(v_params_1886_);
v_a_1934_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1907_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1907_);
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
lean_dec_ref(v_struct_1903_);
lean_dec_ref(v_params_1886_);
v_a_1942_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1905_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1905_);
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
}
else
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Expr_getAppFn(v_e_1888_);
if (lean_obj_tag(v___x_1954_) == 4)
{
lean_object* v_declName_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2006_; 
v_declName_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_declName_1955_);
lean_dec_ref_known(v___x_1954_, 2);
v___x_1956_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1955_, v_a_1893_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2006_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2006_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___y_1962_; lean_object* v___y_1963_; 
if (lean_obj_tag(v_a_1957_) == 1)
{
lean_object* v_val_1991_; lean_object* v_ctorName_1992_; lean_object* v_numParams_1993_; lean_object* v_i_1994_; uint8_t v___y_1996_; uint8_t v___x_2004_; 
v_val_1991_ = lean_ctor_get(v_a_1957_, 0);
lean_inc(v_val_1991_);
lean_dec_ref_known(v_a_1957_, 1);
v_ctorName_1992_ = lean_ctor_get(v_val_1991_, 0);
lean_inc(v_ctorName_1992_);
v_numParams_1993_ = lean_ctor_get(v_val_1991_, 1);
lean_inc(v_numParams_1993_);
v_i_1994_ = lean_ctor_get(v_val_1991_, 2);
lean_inc(v_i_1994_);
lean_dec(v_val_1991_);
v___x_2004_ = lean_name_eq(v_ctorName_1992_, v_ctor_1884_);
lean_dec(v_ctorName_1992_);
if (v___x_2004_ == 0)
{
lean_dec(v_i_1994_);
v___y_1996_ = v___x_2004_;
goto v___jp_1995_;
}
else
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_nat_dec_eq(v_i_1994_, v_idx_1887_);
lean_dec(v_i_1994_);
v___y_1996_ = v___x_2005_;
goto v___jp_1995_;
}
v___jp_1995_:
{
if (v___y_1996_ == 0)
{
lean_dec(v_numParams_1993_);
lean_del_object(v___x_1959_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_params_1886_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1997_ = l_Lean_Expr_getAppNumArgs(v_e_1888_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_add(v_numParams_1993_, v___x_1998_);
lean_dec(v_numParams_1993_);
v___x_2000_ = lean_nat_dec_eq(v___x_1997_, v___x_1999_);
lean_dec(v___x_1999_);
lean_dec(v___x_1997_);
if (v___x_2000_ == 0)
{
lean_del_object(v___x_1959_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_params_1886_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Expr_appArg_x21(v_e_1888_);
if (lean_obj_tag(v_x_x3f_1889_) == 0)
{
v___y_1962_ = v___x_1998_;
v___y_1963_ = v___x_2001_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_2002_; uint8_t v___x_2003_; 
v_val_2002_ = lean_ctor_get(v_x_x3f_1889_, 0);
v___x_2003_ = lean_expr_eqv(v_val_2002_, v___x_2001_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1959_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_params_1886_);
goto v___jp_1898_;
}
else
{
v___y_1962_ = v___x_1998_;
v___y_1963_ = v___x_2001_;
goto v___jp_1961_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_params_1886_);
goto v___jp_1898_;
}
v___jp_1961_:
{
lean_object* v___x_1964_; lean_object* v_dummy_1965_; lean_object* v_nargs_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1964_ = l_Lean_Expr_appFn_x21(v_e_1888_);
lean_dec_ref(v_e_1888_);
v_dummy_1965_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1966_ = l_Lean_Expr_getAppNumArgs(v___x_1964_);
lean_inc(v_nargs_1966_);
v___x_1967_ = lean_mk_array(v_nargs_1966_, v_dummy_1965_);
v___x_1968_ = lean_nat_sub(v_nargs_1966_, v___y_1962_);
lean_dec(v_nargs_1966_);
v___x_1969_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1964_, v___x_1967_, v___x_1968_);
v___x_1970_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1886_, v___x_1969_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1982_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1982_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_unbox(v_a_1971_);
lean_dec(v_a_1971_);
if (v___x_1975_ == 0)
{
lean_del_object(v___x_1973_);
lean_dec_ref(v___y_1963_);
lean_del_object(v___x_1959_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_1977_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v___y_1963_);
v___x_1977_ = v___x_1959_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___y_1963_);
v___x_1977_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1977_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v___y_1963_);
lean_del_object(v___x_1959_);
v_a_1983_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1970_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1970_);
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
}
}
else
{
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_e_1888_);
lean_dec_ref(v_params_1886_);
goto v___jp_1898_;
}
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2007_, lean_object* v_induct_2008_, lean_object* v_params_2009_, lean_object* v_idx_2010_, lean_object* v_e_2011_, lean_object* v_x_x3f_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2007_, v_induct_2008_, v_params_2009_, v_idx_2010_, v_e_2011_, v_x_x3f_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_x_x3f_2012_);
lean_dec(v_idx_2010_);
lean_dec(v_induct_2008_);
lean_dec(v_ctor_2007_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; lean_object* v_env_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2025_ = lean_st_ref_get(v___y_2023_);
v_env_2029_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2025_);
v___x_2030_ = 0;
v___x_2031_ = l_Lean_Environment_findAsync_x3f(v_env_2029_, v_constName_2019_, v___x_2030_);
if (lean_obj_tag(v___x_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2051_; 
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v_kind_2036_; 
v_kind_2036_ = lean_ctor_get_uint8(v_val_2032_, sizeof(void*)*3);
if (v_kind_2036_ == 6)
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2032_);
if (lean_obj_tag(v___x_2037_) == 6)
{
lean_object* v_val_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2048_; 
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_val_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2048_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_val_2038_);
v___x_2043_ = v___x_2034_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_val_2038_);
v___x_2043_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2045_ = v___x_2040_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v___x_2037_);
lean_del_object(v___x_2034_);
v___x_2049_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2050_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2049_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
return v___x_2050_;
}
}
else
{
lean_del_object(v___x_2034_);
lean_dec(v_val_2032_);
goto v___jp_2026_;
}
}
}
else
{
lean_dec(v___x_2031_);
goto v___jp_2026_;
}
v___jp_2026_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2067_, lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v_declName_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v_a_2073_, lean_object* v_val_2074_, lean_object* v_a_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_lt(v_a_2075_, v_upperBound_2067_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec(v_a_2075_);
lean_dec_ref(v___x_2072_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_b_2076_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v_b_2076_);
v___x_2084_ = l_Lean_instInhabitedExpr;
v___x_2085_ = lean_nat_add(v___x_2068_, v_a_2075_);
v___x_2086_ = lean_array_get_borrowed(v___x_2084_, v___x_2069_, v___x_2085_);
lean_dec(v___x_2085_);
lean_inc(v___x_2086_);
lean_inc_ref(v___x_2072_);
v___x_2087_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2070_, v___x_2071_, v___x_2072_, v_a_2075_, v___x_2086_, v_a_2073_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2106_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2106_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2106_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
if (lean_obj_tag(v_a_2088_) == 1)
{
lean_object* v_val_2092_; uint8_t v___x_2093_; 
v_val_2092_ = lean_ctor_get(v_a_2088_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v_a_2088_, 1);
v___x_2093_ = lean_expr_eqv(v_val_2092_, v_val_2074_);
lean_dec(v_val_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_dec(v_a_2075_);
lean_dec_ref(v___x_2072_);
v___x_2094_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2094_);
v___x_2096_ = v___x_2090_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_del_object(v___x_2090_);
v___x_2098_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_nat_add(v_a_2075_, v___x_2099_);
lean_dec(v_a_2075_);
v_a_2075_ = v___x_2100_;
v_b_2076_ = v___x_2098_;
goto _start;
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec(v_a_2088_);
lean_dec(v_a_2075_);
lean_dec_ref(v___x_2072_);
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2102_);
v___x_2104_ = v___x_2090_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
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
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_a_2075_);
lean_dec_ref(v___x_2072_);
v_a_2107_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2087_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2087_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2115_, lean_object* v___x_2116_, lean_object* v___x_2117_, lean_object* v_declName_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v_a_2121_, lean_object* v_val_2122_, lean_object* v_a_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2115_, v___x_2116_, v___x_2117_, v_declName_2118_, v___x_2119_, v___x_2120_, v_a_2121_, v_val_2122_, v_a_2123_, v_b_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_val_2122_);
lean_dec(v_a_2121_);
lean_dec(v___x_2119_);
lean_dec(v_declName_2118_);
lean_dec_ref(v___x_2117_);
lean_dec(v___x_2116_);
lean_dec(v_upperBound_2115_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2131_, lean_object* v_p_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Expr_getAppFn(v_e_2131_);
if (lean_obj_tag(v___x_2138_) == 4)
{
lean_object* v_declName_2139_; lean_object* v___x_2140_; 
v_declName_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_n(v_declName_2139_, 2);
lean_dec_ref_known(v___x_2138_, 2);
v___x_2140_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2139_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2213_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2213_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2213_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
if (lean_obj_tag(v_a_2141_) == 1)
{
lean_object* v_val_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2210_; 
v_val_2150_ = lean_ctor_get(v_a_2141_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2152_ = v_a_2141_;
v_isShared_2153_ = v_isSharedCheck_2210_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_val_2150_);
lean_dec(v_a_2141_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2210_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_induct_2154_; lean_object* v_numParams_2155_; lean_object* v_numFields_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_induct_2154_ = lean_ctor_get(v_val_2150_, 1);
lean_inc_n(v_induct_2154_, 2);
v_numParams_2155_ = lean_ctor_get(v_val_2150_, 3);
lean_inc(v_numParams_2155_);
v_numFields_2156_ = lean_ctor_get(v_val_2150_, 4);
lean_inc(v_numFields_2156_);
lean_dec(v_val_2150_);
v___x_2157_ = lean_apply_1(v_p_2132_, v_induct_2154_);
v___x_2158_ = lean_unbox(v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_numFields_2156_);
lean_dec(v_numParams_2155_);
lean_dec(v_induct_2154_);
lean_del_object(v___x_2143_);
lean_dec(v_declName_2139_);
lean_dec_ref(v_e_2131_);
v___x_2159_ = lean_box(0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2159_);
v___x_2161_ = v___x_2152_;
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
else
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
lean_del_object(v___x_2152_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_nat_dec_lt(v___x_2163_, v_numFields_2156_);
if (v___x_2164_ == 0)
{
lean_dec(v_numFields_2156_);
lean_dec(v_numParams_2155_);
lean_dec(v_induct_2154_);
lean_dec(v_declName_2139_);
lean_dec_ref(v_e_2131_);
goto v___jp_2145_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = l_Lean_Expr_getAppNumArgs(v_e_2131_);
v___x_2166_ = lean_nat_add(v_numParams_2155_, v_numFields_2156_);
v___x_2167_ = lean_nat_dec_eq(v___x_2165_, v___x_2166_);
lean_dec(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_dec(v___x_2165_);
lean_dec(v_numFields_2156_);
lean_dec(v_numParams_2155_);
lean_dec(v_induct_2154_);
lean_dec(v_declName_2139_);
lean_dec_ref(v_e_2131_);
goto v___jp_2145_;
}
else
{
lean_object* v___x_2168_; lean_object* v_dummy_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2143_);
v___x_2168_ = l_Lean_instInhabitedExpr;
v_dummy_2169_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2165_);
v___x_2170_ = lean_mk_array(v___x_2165_, v_dummy_2169_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_sub(v___x_2165_, v___x_2171_);
lean_dec(v___x_2165_);
v___x_2173_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2131_, v___x_2170_, v___x_2172_);
lean_inc(v_numParams_2155_);
v___x_2174_ = l_Array_extract___redArg(v___x_2173_, v___x_2163_, v_numParams_2155_);
v___x_2175_ = lean_array_get(v___x_2168_, v___x_2173_, v_numParams_2155_);
v___x_2176_ = lean_box(0);
lean_inc_ref(v___x_2174_);
v___x_2177_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2139_, v_induct_2154_, v___x_2174_, v___x_2163_, v___x_2175_, v___x_2176_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2209_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2209_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2209_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
if (lean_obj_tag(v_a_2178_) == 1)
{
lean_object* v_val_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2180_);
v_val_2182_ = lean_ctor_get(v_a_2178_, 0);
v___x_2183_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2156_, v_numParams_2155_, v___x_2173_, v_declName_2139_, v_induct_2154_, v___x_2174_, v_a_2178_, v_val_2182_, v___x_2171_, v___x_2183_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_induct_2154_);
lean_dec(v_declName_2139_);
lean_dec_ref(v___x_2173_);
lean_dec(v_numParams_2155_);
lean_dec(v_numFields_2156_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2197_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2197_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2197_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_fst_2189_; 
v_fst_2189_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_fst_2189_);
lean_dec(v_a_2185_);
if (lean_obj_tag(v_fst_2189_) == 0)
{
lean_object* v___x_2191_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_a_2178_);
v___x_2191_ = v___x_2187_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2178_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
lean_object* v_val_2193_; lean_object* v___x_2195_; 
lean_dec_ref_known(v_a_2178_, 1);
v_val_2193_ = lean_ctor_get(v_fst_2189_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v_fst_2189_, 1);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_val_2193_);
v___x_2195_ = v___x_2187_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_val_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref_known(v_a_2178_, 1);
v_a_2198_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2184_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2184_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v___x_2207_; 
lean_dec(v_a_2178_);
lean_dec_ref(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec(v_numFields_2156_);
lean_dec(v_numParams_2155_);
lean_dec(v_induct_2154_);
lean_dec(v_declName_2139_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2176_);
v___x_2207_ = v___x_2180_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2176_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_dec_ref(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec(v_numFields_2156_);
lean_dec(v_numParams_2155_);
lean_dec(v_induct_2154_);
lean_dec(v_declName_2139_);
return v___x_2177_;
}
}
}
}
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
lean_dec(v_declName_2139_);
lean_dec_ref(v_p_2132_);
lean_dec_ref(v_e_2131_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
v___jp_2145_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_box(0);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2146_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_declName_2139_);
lean_dec_ref(v_p_2132_);
lean_dec_ref(v_e_2131_);
v_a_2214_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2140_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2140_);
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
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v___x_2138_);
lean_dec_ref(v_p_2132_);
lean_dec_ref(v_e_2131_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2224_, lean_object* v_p_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_etaStruct_x3f(v_e_2224_, v_p_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2232_, lean_object* v___x_2233_, lean_object* v___x_2234_, lean_object* v_declName_2235_, lean_object* v___x_2236_, lean_object* v___x_2237_, lean_object* v_a_2238_, lean_object* v_val_2239_, lean_object* v_inst_2240_, lean_object* v_R_2241_, lean_object* v_a_2242_, lean_object* v_b_2243_, lean_object* v_c_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2232_, v___x_2233_, v___x_2234_, v_declName_2235_, v___x_2236_, v___x_2237_, v_a_2238_, v_val_2239_, v_a_2242_, v_b_2243_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2251_ = _args[0];
lean_object* v___x_2252_ = _args[1];
lean_object* v___x_2253_ = _args[2];
lean_object* v_declName_2254_ = _args[3];
lean_object* v___x_2255_ = _args[4];
lean_object* v___x_2256_ = _args[5];
lean_object* v_a_2257_ = _args[6];
lean_object* v_val_2258_ = _args[7];
lean_object* v_inst_2259_ = _args[8];
lean_object* v_R_2260_ = _args[9];
lean_object* v_a_2261_ = _args[10];
lean_object* v_b_2262_ = _args[11];
lean_object* v_c_2263_ = _args[12];
lean_object* v___y_2264_ = _args[13];
lean_object* v___y_2265_ = _args[14];
lean_object* v___y_2266_ = _args[15];
lean_object* v___y_2267_ = _args[16];
lean_object* v___y_2268_ = _args[17];
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2251_, v___x_2252_, v___x_2253_, v_declName_2254_, v___x_2255_, v___x_2256_, v_a_2257_, v_val_2258_, v_inst_2259_, v_R_2260_, v_a_2261_, v_b_2262_, v_c_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_val_2258_);
lean_dec(v_a_2257_);
lean_dec(v___x_2255_);
lean_dec(v_declName_2254_);
lean_dec_ref(v___x_2253_);
lean_dec(v___x_2252_);
lean_dec(v_upperBound_2251_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Lean_Expr_hasMVar(v_e_2270_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_e_2270_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; lean_object* v_mctx_2276_; lean_object* v___x_2277_; lean_object* v_fst_2278_; lean_object* v_snd_2279_; lean_object* v___x_2280_; lean_object* v_cache_2281_; lean_object* v_zetaDeltaFVarIds_2282_; lean_object* v_postponed_2283_; lean_object* v_diag_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2293_; 
v___x_2275_ = lean_st_ref_get(v___y_2271_);
v_mctx_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_mctx_2276_);
lean_dec(v___x_2275_);
v___x_2277_ = l_Lean_instantiateMVarsCore(v_mctx_2276_, v_e_2270_);
v_fst_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_fst_2278_);
v_snd_2279_ = lean_ctor_get(v___x_2277_, 1);
lean_inc(v_snd_2279_);
lean_dec_ref(v___x_2277_);
v___x_2280_ = lean_st_ref_take(v___y_2271_);
v_cache_2281_ = lean_ctor_get(v___x_2280_, 1);
v_zetaDeltaFVarIds_2282_ = lean_ctor_get(v___x_2280_, 2);
v_postponed_2283_ = lean_ctor_get(v___x_2280_, 3);
v_diag_2284_ = lean_ctor_get(v___x_2280_, 4);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v___x_2280_, 0);
lean_dec(v_unused_2294_);
v___x_2286_ = v___x_2280_;
v_isShared_2287_ = v_isSharedCheck_2293_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_diag_2284_);
lean_inc(v_postponed_2283_);
lean_inc(v_zetaDeltaFVarIds_2282_);
lean_inc(v_cache_2281_);
lean_dec(v___x_2280_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2293_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_snd_2279_);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_snd_2279_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_cache_2281_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_zetaDeltaFVarIds_2282_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_postponed_2283_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_diag_2284_);
v___x_2289_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_st_ref_put(v___y_2271_, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_fst_2278_);
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2295_, v___y_2296_);
lean_dec(v___y_2296_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2299_, v___y_2301_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_x_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2330_, lean_object* v_e_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Meta_etaStruct_x3f(v_e_2331_, v_p_2330_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2357_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2357_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2357_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
if (lean_obj_tag(v_a_2338_) == 1)
{
lean_object* v_val_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2352_; 
v_val_2342_ = lean_ctor_get(v_a_2338_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_a_2338_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2344_ = v_a_2338_;
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_val_2342_);
lean_dec(v_a_2338_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2352_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 0);
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_val_2342_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2347_);
v___x_2349_ = v___x_2340_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
lean_dec(v_a_2338_);
v___x_2353_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2353_);
v___x_2355_ = v___x_2340_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2337_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2337_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2366_, lean_object* v_e_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2366_, v_e_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_apply_1(v_x_2375_, lean_box(0));
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2383_, v_x_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2391_, lean_object* v_b_2392_, lean_object* v_x_2393_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_dec(v_b_2392_);
lean_dec_ref(v_a_2391_);
return v_x_2393_;
}
else
{
lean_object* v_key_2394_; lean_object* v_value_2395_; lean_object* v_tail_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2408_; 
v_key_2394_ = lean_ctor_get(v_x_2393_, 0);
v_value_2395_ = lean_ctor_get(v_x_2393_, 1);
v_tail_2396_ = lean_ctor_get(v_x_2393_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_x_2393_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2398_ = v_x_2393_;
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_tail_2396_);
lean_inc(v_value_2395_);
lean_inc(v_key_2394_);
lean_dec(v_x_2393_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
uint8_t v___x_2400_; 
v___x_2400_ = l_Lean_ExprStructEq_beq(v_key_2394_, v_a_2391_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2391_, v_b_2392_, v_tail_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 2, v___x_2401_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_key_2394_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_value_2395_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
else
{
lean_object* v___x_2406_; 
lean_dec(v_value_2395_);
lean_dec(v_key_2394_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_b_2392_);
lean_ctor_set(v___x_2398_, 0, v_a_2391_);
v___x_2406_ = v___x_2398_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2391_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_b_2392_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_tail_2396_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
return v_x_2409_;
}
else
{
lean_object* v_key_2411_; lean_object* v_value_2412_; lean_object* v_tail_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2436_; 
v_key_2411_ = lean_ctor_get(v_x_2410_, 0);
v_value_2412_ = lean_ctor_get(v_x_2410_, 1);
v_tail_2413_ = lean_ctor_get(v_x_2410_, 2);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_x_2410_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2415_ = v_x_2410_;
v_isShared_2416_ = v_isSharedCheck_2436_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_tail_2413_);
lean_inc(v_value_2412_);
lean_inc(v_key_2411_);
lean_dec(v_x_2410_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2436_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; uint64_t v___x_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; uint64_t v_fold_2421_; uint64_t v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; size_t v___x_2427_; size_t v___x_2428_; size_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2417_ = lean_array_get_size(v_x_2409_);
v___x_2418_ = l_Lean_ExprStructEq_hash(v_key_2411_);
v___x_2419_ = 32ULL;
v___x_2420_ = lean_uint64_shift_right(v___x_2418_, v___x_2419_);
v_fold_2421_ = lean_uint64_xor(v___x_2418_, v___x_2420_);
v___x_2422_ = 16ULL;
v___x_2423_ = lean_uint64_shift_right(v_fold_2421_, v___x_2422_);
v___x_2424_ = lean_uint64_xor(v_fold_2421_, v___x_2423_);
v___x_2425_ = lean_uint64_to_usize(v___x_2424_);
v___x_2426_ = lean_usize_of_nat(v___x_2417_);
v___x_2427_ = ((size_t)1ULL);
v___x_2428_ = lean_usize_sub(v___x_2426_, v___x_2427_);
v___x_2429_ = lean_usize_land(v___x_2425_, v___x_2428_);
v___x_2430_ = lean_array_uget_borrowed(v_x_2409_, v___x_2429_);
lean_inc(v___x_2430_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 2, v___x_2430_);
v___x_2432_ = v___x_2415_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_key_2411_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_value_2412_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_array_uset(v_x_2409_, v___x_2429_, v___x_2432_);
v_x_2409_ = v___x_2433_;
v_x_2410_ = v_tail_2413_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2437_, lean_object* v_source_2438_, lean_object* v_target_2439_){
_start:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_array_get_size(v_source_2438_);
v___x_2441_ = lean_nat_dec_lt(v_i_2437_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_dec_ref(v_source_2438_);
lean_dec(v_i_2437_);
return v_target_2439_;
}
else
{
lean_object* v_es_2442_; lean_object* v___x_2443_; lean_object* v_source_2444_; lean_object* v_target_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_es_2442_ = lean_array_fget(v_source_2438_, v_i_2437_);
v___x_2443_ = lean_box(0);
v_source_2444_ = lean_array_fset(v_source_2438_, v_i_2437_, v___x_2443_);
v_target_2445_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2439_, v_es_2442_);
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_nat_add(v_i_2437_, v___x_2446_);
lean_dec(v_i_2437_);
v_i_2437_ = v___x_2447_;
v_source_2438_ = v_source_2444_;
v_target_2439_ = v_target_2445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_nbuckets_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2450_ = lean_array_get_size(v_data_2449_);
v___x_2451_ = lean_unsigned_to_nat(2u);
v_nbuckets_2452_ = lean_nat_mul(v___x_2450_, v___x_2451_);
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_mk_array(v_nbuckets_2452_, v___x_2454_);
v___x_2456_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2453_, v_data_2449_, v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2457_, lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 0)
{
uint8_t v___x_2459_; 
v___x_2459_ = 0;
return v___x_2459_;
}
else
{
lean_object* v_key_2460_; lean_object* v_tail_2461_; uint8_t v___x_2462_; 
v_key_2460_ = lean_ctor_get(v_x_2458_, 0);
v_tail_2461_ = lean_ctor_get(v_x_2458_, 2);
v___x_2462_ = l_Lean_ExprStructEq_beq(v_key_2460_, v_a_2457_);
if (v___x_2462_ == 0)
{
v_x_2458_ = v_tail_2461_;
goto _start;
}
else
{
return v___x_2462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2464_, lean_object* v_x_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2464_, v_x_2465_);
lean_dec(v_x_2465_);
lean_dec_ref(v_a_2464_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2468_, lean_object* v_a_2469_, lean_object* v_b_2470_){
_start:
{
lean_object* v_size_2471_; lean_object* v_buckets_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2515_; 
v_size_2471_ = lean_ctor_get(v_m_2468_, 0);
v_buckets_2472_ = lean_ctor_get(v_m_2468_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_m_2468_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2474_ = v_m_2468_;
v_isShared_2475_ = v_isSharedCheck_2515_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_buckets_2472_);
lean_inc(v_size_2471_);
lean_dec(v_m_2468_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2515_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; uint64_t v___x_2477_; uint64_t v___x_2478_; uint64_t v___x_2479_; uint64_t v_fold_2480_; uint64_t v___x_2481_; uint64_t v___x_2482_; uint64_t v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; size_t v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; lean_object* v_bkt_2489_; uint8_t v___x_2490_; 
v___x_2476_ = lean_array_get_size(v_buckets_2472_);
v___x_2477_ = l_Lean_ExprStructEq_hash(v_a_2469_);
v___x_2478_ = 32ULL;
v___x_2479_ = lean_uint64_shift_right(v___x_2477_, v___x_2478_);
v_fold_2480_ = lean_uint64_xor(v___x_2477_, v___x_2479_);
v___x_2481_ = 16ULL;
v___x_2482_ = lean_uint64_shift_right(v_fold_2480_, v___x_2481_);
v___x_2483_ = lean_uint64_xor(v_fold_2480_, v___x_2482_);
v___x_2484_ = lean_uint64_to_usize(v___x_2483_);
v___x_2485_ = lean_usize_of_nat(v___x_2476_);
v___x_2486_ = ((size_t)1ULL);
v___x_2487_ = lean_usize_sub(v___x_2485_, v___x_2486_);
v___x_2488_ = lean_usize_land(v___x_2484_, v___x_2487_);
v_bkt_2489_ = lean_array_uget_borrowed(v_buckets_2472_, v___x_2488_);
v___x_2490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2469_, v_bkt_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v_size_x27_2492_; lean_object* v___x_2493_; lean_object* v_buckets_x27_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v_size_x27_2492_ = lean_nat_add(v_size_2471_, v___x_2491_);
lean_dec(v_size_2471_);
lean_inc(v_bkt_2489_);
v___x_2493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2493_, 0, v_a_2469_);
lean_ctor_set(v___x_2493_, 1, v_b_2470_);
lean_ctor_set(v___x_2493_, 2, v_bkt_2489_);
v_buckets_x27_2494_ = lean_array_uset(v_buckets_2472_, v___x_2488_, v___x_2493_);
v___x_2495_ = lean_unsigned_to_nat(4u);
v___x_2496_ = lean_nat_mul(v_size_x27_2492_, v___x_2495_);
v___x_2497_ = lean_unsigned_to_nat(3u);
v___x_2498_ = lean_nat_div(v___x_2496_, v___x_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_array_get_size(v_buckets_x27_2494_);
v___x_2500_ = lean_nat_dec_le(v___x_2498_, v___x_2499_);
lean_dec(v___x_2498_);
if (v___x_2500_ == 0)
{
lean_object* v_val_2501_; lean_object* v___x_2503_; 
v_val_2501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2494_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v_val_2501_);
lean_ctor_set(v___x_2474_, 0, v_size_x27_2492_);
v___x_2503_ = v___x_2474_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_size_x27_2492_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_val_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
else
{
lean_object* v___x_2506_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v_buckets_x27_2494_);
lean_ctor_set(v___x_2474_, 0, v_size_x27_2492_);
v___x_2506_ = v___x_2474_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_size_x27_2492_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_buckets_x27_2494_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
else
{
lean_object* v___x_2508_; lean_object* v_buckets_x27_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
lean_inc(v_bkt_2489_);
v___x_2508_ = lean_box(0);
v_buckets_x27_2509_ = lean_array_uset(v_buckets_2472_, v___x_2488_, v___x_2508_);
v___x_2510_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2469_, v_b_2470_, v_bkt_2489_);
v___x_2511_ = lean_array_uset(v_buckets_x27_2509_, v___x_2488_, v___x_2510_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___x_2511_);
v___x_2513_ = v___x_2474_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_size_2471_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2516_, lean_object* v_e_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2520_ = lean_st_ref_take(v_a_2516_);
v___x_2521_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2520_, v_e_2517_, v_a_2518_);
v___x_2522_ = lean_st_ref_put(v_a_2516_, v___x_2521_);
v___x_2523_ = lean_box(0);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2524_, v_e_2525_, v_a_2526_);
lean_dec(v_a_2524_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2529_, lean_object* v_x_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_apply_1(v_x_2530_, lean_box(0));
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2538_, lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2538_, v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2546_, lean_object* v_x_2547_){
_start:
{
if (lean_obj_tag(v_x_2547_) == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
return v___x_2548_;
}
else
{
lean_object* v_key_2549_; lean_object* v_value_2550_; lean_object* v_tail_2551_; uint8_t v___x_2552_; 
v_key_2549_ = lean_ctor_get(v_x_2547_, 0);
v_value_2550_ = lean_ctor_get(v_x_2547_, 1);
v_tail_2551_ = lean_ctor_get(v_x_2547_, 2);
v___x_2552_ = l_Lean_ExprStructEq_beq(v_key_2549_, v_a_2546_);
if (v___x_2552_ == 0)
{
v_x_2547_ = v_tail_2551_;
goto _start;
}
else
{
lean_object* v___x_2554_; 
lean_inc(v_value_2550_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_value_2550_);
return v___x_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2555_, lean_object* v_x_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2555_, v_x_2556_);
lean_dec(v_x_2556_);
lean_dec_ref(v_a_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_buckets_2560_; lean_object* v___x_2561_; uint64_t v___x_2562_; uint64_t v___x_2563_; uint64_t v___x_2564_; uint64_t v_fold_2565_; uint64_t v___x_2566_; uint64_t v___x_2567_; uint64_t v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; size_t v___x_2571_; size_t v___x_2572_; size_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_buckets_2560_ = lean_ctor_get(v_m_2558_, 1);
v___x_2561_ = lean_array_get_size(v_buckets_2560_);
v___x_2562_ = l_Lean_ExprStructEq_hash(v_a_2559_);
v___x_2563_ = 32ULL;
v___x_2564_ = lean_uint64_shift_right(v___x_2562_, v___x_2563_);
v_fold_2565_ = lean_uint64_xor(v___x_2562_, v___x_2564_);
v___x_2566_ = 16ULL;
v___x_2567_ = lean_uint64_shift_right(v_fold_2565_, v___x_2566_);
v___x_2568_ = lean_uint64_xor(v_fold_2565_, v___x_2567_);
v___x_2569_ = lean_uint64_to_usize(v___x_2568_);
v___x_2570_ = lean_usize_of_nat(v___x_2561_);
v___x_2571_ = ((size_t)1ULL);
v___x_2572_ = lean_usize_sub(v___x_2570_, v___x_2571_);
v___x_2573_ = lean_usize_land(v___x_2569_, v___x_2572_);
v___x_2574_ = lean_array_uget_borrowed(v_buckets_2560_, v___x_2573_);
v___x_2575_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2559_, v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2576_, v_a_2577_);
lean_dec_ref(v_a_2577_);
lean_dec_ref(v_m_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2579_, lean_object* v___y_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
lean_inc(v___y_2585_);
lean_inc_ref(v___y_2584_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc(v___y_2580_);
v___x_2587_ = lean_apply_7(v_k_2579_, v_b_2581_, v___y_2580_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, lean_box(0));
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2588_, lean_object* v___y_2589_, lean_object* v_b_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2588_, v___y_2589_, v_b_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2589_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2597_, uint8_t v_bi_2598_, lean_object* v_type_2599_, lean_object* v_k_2600_, uint8_t v_kind_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___f_2608_; lean_object* v___x_2609_; 
lean_inc(v___y_2602_);
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2608_, 0, v_k_2600_);
lean_closure_set(v___f_2608_, 1, v___y_2602_);
v___x_2609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2597_, v_bi_2598_, v_type_2599_, v___f_2608_, v_kind_2601_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2609_) == 0)
{
return v___x_2609_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2618_, lean_object* v_bi_2619_, lean_object* v_type_2620_, lean_object* v_k_2621_, lean_object* v_kind_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
uint8_t v_bi_boxed_2629_; uint8_t v_kind_boxed_2630_; lean_object* v_res_2631_; 
v_bi_boxed_2629_ = lean_unbox(v_bi_2619_);
v_kind_boxed_2630_ = lean_unbox(v_kind_2622_);
v_res_2631_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2618_, v_bi_boxed_2629_, v_type_2620_, v_k_2621_, v_kind_boxed_2630_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2632_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2646_, lean_object* v_type_2647_, lean_object* v_val_2648_, lean_object* v_k_2649_, uint8_t v_nondep_2650_, uint8_t v_kind_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___f_2658_; lean_object* v___x_2659_; 
lean_inc(v___y_2652_);
v___f_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2658_, 0, v_k_2649_);
lean_closure_set(v___f_2658_, 1, v___y_2652_);
v___x_2659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2646_, v_type_2647_, v_val_2648_, v___f_2658_, v_nondep_2650_, v_kind_2651_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2659_) == 0)
{
return v___x_2659_;
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2668_, lean_object* v_type_2669_, lean_object* v_val_2670_, lean_object* v_k_2671_, lean_object* v_nondep_2672_, lean_object* v_kind_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v_nondep_boxed_2680_; uint8_t v_kind_boxed_2681_; lean_object* v_res_2682_; 
v_nondep_boxed_2680_ = lean_unbox(v_nondep_2672_);
v_kind_boxed_2681_ = lean_unbox(v_kind_2673_);
v_res_2682_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2668_, v_type_2669_, v_val_2670_, v_k_2671_, v_nondep_boxed_2680_, v_kind_boxed_2681_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
return v_res_2682_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = l_Lean_maxRecDepthErrorMessage;
v___x_2689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2691_ = l_Lean_MessageData_ofFormat(v___x_2690_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2693_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2694_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2695_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_ref_2695_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___y_2711_; lean_object* v_toCold_2720_; lean_object* v_currRecDepth_2721_; lean_object* v_ref_2722_; uint8_t v_diag_2723_; uint8_t v_suppressElabErrors_2724_; lean_object* v_maxRecDepth_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_toCold_2720_ = lean_ctor_get(v___y_2707_, 0);
v_currRecDepth_2721_ = lean_ctor_get(v___y_2707_, 1);
v_ref_2722_ = lean_ctor_get(v___y_2707_, 2);
v_diag_2723_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*3);
v_suppressElabErrors_2724_ = lean_ctor_get_uint8(v___y_2707_, sizeof(void*)*3 + 1);
v_maxRecDepth_2730_ = lean_ctor_get(v_toCold_2720_, 3);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_nat_dec_eq(v_maxRecDepth_2730_, v___x_2731_);
if (v___x_2732_ == 0)
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_nat_dec_eq(v_currRecDepth_2721_, v_maxRecDepth_2730_);
if (v___x_2733_ == 0)
{
goto v___jp_2725_;
}
else
{
lean_object* v___x_2734_; 
lean_dec_ref(v_x_2703_);
lean_inc(v_ref_2722_);
v___x_2734_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2722_);
v___y_2711_ = v___x_2734_;
goto v___jp_2710_;
}
}
else
{
goto v___jp_2725_;
}
v___jp_2710_:
{
if (lean_obj_tag(v___y_2711_) == 0)
{
return v___y_2711_;
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_a_2712_ = lean_ctor_get(v___y_2711_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___y_2711_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___y_2711_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___y_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
v___jp_2725_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_currRecDepth_2721_, v___x_2726_);
lean_inc(v_ref_2722_);
lean_inc_ref(v_toCold_2720_);
v___x_2728_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2728_, 0, v_toCold_2720_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
lean_ctor_set(v___x_2728_, 2, v_ref_2722_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*3, v_diag_2723_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*3 + 1, v_suppressElabErrors_2724_);
lean_inc(v___y_2708_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
v___x_2729_ = lean_apply_6(v_x_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___x_2728_, v___y_2708_, lean_box(0));
v___y_2711_ = v___x_2729_;
goto v___jp_2710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2746_, lean_object* v_pre_2747_, lean_object* v_post_2748_, uint8_t v_usedLetOnly_2749_, uint8_t v_skipConstInApp_2750_, uint8_t v_skipInstances_2751_, lean_object* v_body_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_array_push(v_fvars_2746_, v_x_2753_);
v___x_2761_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2747_, v_post_2748_, v_usedLetOnly_2749_, v_skipConstInApp_2750_, v_skipInstances_2751_, v___x_2760_, v_body_2752_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2762_, lean_object* v_pre_2763_, lean_object* v_post_2764_, lean_object* v_usedLetOnly_2765_, lean_object* v_skipConstInApp_2766_, lean_object* v_skipInstances_2767_, lean_object* v_body_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v_usedLetOnly_boxed_2776_; uint8_t v_skipConstInApp_boxed_2777_; uint8_t v_skipInstances_boxed_2778_; lean_object* v_res_2779_; 
v_usedLetOnly_boxed_2776_ = lean_unbox(v_usedLetOnly_2765_);
v_skipConstInApp_boxed_2777_ = lean_unbox(v_skipConstInApp_2766_);
v_skipInstances_boxed_2778_ = lean_unbox(v_skipInstances_2767_);
v_res_2779_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2762_, v_pre_2763_, v_post_2764_, v_usedLetOnly_boxed_2776_, v_skipConstInApp_boxed_2777_, v_skipInstances_boxed_2778_, v_body_2768_, v_x_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2780_, lean_object* v_post_2781_, uint8_t v_usedLetOnly_2782_, uint8_t v_skipConstInApp_2783_, uint8_t v_skipInstances_2784_, lean_object* v_e_2785_, lean_object* v_a_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
lean_inc_ref(v_post_2781_);
lean_inc(v___y_2790_);
lean_inc_ref(v___y_2789_);
lean_inc(v___y_2788_);
lean_inc_ref(v___y_2787_);
lean_inc_ref(v_e_2785_);
v___x_2792_ = lean_apply_6(v_post_2781_, v_e_2785_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, lean_box(0));
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2811_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2811_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2811_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
switch(lean_obj_tag(v_a_2793_))
{
case 0:
{
lean_object* v_e_2797_; lean_object* v___x_2799_; 
lean_dec_ref(v_e_2785_);
lean_dec_ref(v_post_2781_);
lean_dec_ref(v_pre_2780_);
v_e_2797_ = lean_ctor_get(v_a_2793_, 0);
lean_inc_ref(v_e_2797_);
lean_dec_ref_known(v_a_2793_, 1);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_e_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_e_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
case 1:
{
lean_object* v_e_2801_; lean_object* v___x_2802_; 
lean_del_object(v___x_2795_);
lean_dec_ref(v_e_2785_);
v_e_2801_ = lean_ctor_get(v_a_2793_, 0);
lean_inc_ref(v_e_2801_);
lean_dec_ref_known(v_a_2793_, 1);
v___x_2802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2780_, v_post_2781_, v_usedLetOnly_2782_, v_skipConstInApp_2783_, v_skipInstances_2784_, v_e_2801_, v_a_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2802_;
}
default: 
{
lean_object* v_e_x3f_2803_; 
lean_dec_ref(v_post_2781_);
lean_dec_ref(v_pre_2780_);
v_e_x3f_2803_ = lean_ctor_get(v_a_2793_, 0);
lean_inc(v_e_x3f_2803_);
lean_dec_ref_known(v_a_2793_, 1);
if (lean_obj_tag(v_e_x3f_2803_) == 0)
{
lean_object* v___x_2805_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_e_2785_);
v___x_2805_ = v___x_2795_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_e_2785_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
else
{
lean_object* v_val_2807_; lean_object* v___x_2809_; 
lean_dec_ref(v_e_2785_);
v_val_2807_ = lean_ctor_get(v_e_x3f_2803_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v_e_x3f_2803_, 1);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_val_2807_);
v___x_2809_ = v___x_2795_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_val_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v_e_2785_);
lean_dec_ref(v_post_2781_);
lean_dec_ref(v_pre_2780_);
v_a_2812_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2792_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2792_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2820_, lean_object* v_post_2821_, uint8_t v_usedLetOnly_2822_, uint8_t v_skipConstInApp_2823_, uint8_t v_skipInstances_2824_, lean_object* v_fvars_2825_, lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
if (lean_obj_tag(v_e_2826_) == 6)
{
lean_object* v_binderName_2833_; lean_object* v_binderType_2834_; lean_object* v_body_2835_; uint8_t v_binderInfo_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_binderName_2833_ = lean_ctor_get(v_e_2826_, 0);
lean_inc(v_binderName_2833_);
v_binderType_2834_ = lean_ctor_get(v_e_2826_, 1);
lean_inc_ref(v_binderType_2834_);
v_body_2835_ = lean_ctor_get(v_e_2826_, 2);
lean_inc_ref(v_body_2835_);
v_binderInfo_2836_ = lean_ctor_get_uint8(v_e_2826_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2826_, 3);
v___x_2837_ = lean_expr_instantiate_rev(v_binderType_2834_, v_fvars_2825_);
lean_dec_ref(v_binderType_2834_);
lean_inc_ref(v_post_2821_);
lean_inc_ref(v_pre_2820_);
v___x_2838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2820_, v_post_2821_, v_usedLetOnly_2822_, v_skipConstInApp_2823_, v_skipInstances_2824_, v___x_2837_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = lean_box(v_usedLetOnly_2822_);
v___x_2841_ = lean_box(v_skipConstInApp_2823_);
v___x_2842_ = lean_box(v_skipInstances_2824_);
v___f_2843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2843_, 0, v_fvars_2825_);
lean_closure_set(v___f_2843_, 1, v_pre_2820_);
lean_closure_set(v___f_2843_, 2, v_post_2821_);
lean_closure_set(v___f_2843_, 3, v___x_2840_);
lean_closure_set(v___f_2843_, 4, v___x_2841_);
lean_closure_set(v___f_2843_, 5, v___x_2842_);
lean_closure_set(v___f_2843_, 6, v_body_2835_);
v___x_2844_ = 0;
v___x_2845_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2833_, v_binderInfo_2836_, v_a_2839_, v___f_2843_, v___x_2844_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2845_;
}
else
{
lean_dec_ref(v_body_2835_);
lean_dec(v_binderName_2833_);
lean_dec_ref(v_fvars_2825_);
lean_dec_ref(v_post_2821_);
lean_dec_ref(v_pre_2820_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_expr_instantiate_rev(v_e_2826_, v_fvars_2825_);
lean_dec_ref(v_e_2826_);
lean_inc_ref(v_post_2821_);
lean_inc_ref(v_pre_2820_);
v___x_2847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2820_, v_post_2821_, v_usedLetOnly_2822_, v_skipConstInApp_2823_, v_skipInstances_2824_, v___x_2846_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; uint8_t v___x_2849_; uint8_t v___x_2850_; uint8_t v___x_2851_; lean_object* v___x_2852_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = 0;
v___x_2850_ = 1;
v___x_2851_ = 1;
v___x_2852_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2825_, v_a_2848_, v___x_2849_, v_usedLetOnly_2822_, v___x_2849_, v___x_2850_, v___x_2851_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec_ref(v_fvars_2825_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2820_, v_post_2821_, v_usedLetOnly_2822_, v_skipConstInApp_2823_, v_skipInstances_2824_, v_a_2853_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2854_;
}
else
{
lean_dec_ref(v_post_2821_);
lean_dec_ref(v_pre_2820_);
return v___x_2852_;
}
}
else
{
lean_dec_ref(v_fvars_2825_);
lean_dec_ref(v_post_2821_);
lean_dec_ref(v_pre_2820_);
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2855_, lean_object* v_pre_2856_, lean_object* v_post_2857_, uint8_t v_usedLetOnly_2858_, uint8_t v_skipConstInApp_2859_, uint8_t v_skipInstances_2860_, lean_object* v_body_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_array_push(v_fvars_2855_, v_x_2862_);
v___x_2870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2856_, v_post_2857_, v_usedLetOnly_2858_, v_skipConstInApp_2859_, v_skipInstances_2860_, v___x_2869_, v_body_2861_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2871_, lean_object* v_pre_2872_, lean_object* v_post_2873_, lean_object* v_usedLetOnly_2874_, lean_object* v_skipConstInApp_2875_, lean_object* v_skipInstances_2876_, lean_object* v_body_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v_usedLetOnly_boxed_2885_; uint8_t v_skipConstInApp_boxed_2886_; uint8_t v_skipInstances_boxed_2887_; lean_object* v_res_2888_; 
v_usedLetOnly_boxed_2885_ = lean_unbox(v_usedLetOnly_2874_);
v_skipConstInApp_boxed_2886_ = lean_unbox(v_skipConstInApp_2875_);
v_skipInstances_boxed_2887_ = lean_unbox(v_skipInstances_2876_);
v_res_2888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2871_, v_pre_2872_, v_post_2873_, v_usedLetOnly_boxed_2885_, v_skipConstInApp_boxed_2886_, v_skipInstances_boxed_2887_, v_body_2877_, v_x_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2889_, lean_object* v_post_2890_, uint8_t v_usedLetOnly_2891_, uint8_t v_skipConstInApp_2892_, uint8_t v_skipInstances_2893_, lean_object* v_fvars_2894_, lean_object* v_e_2895_, lean_object* v_a_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
if (lean_obj_tag(v_e_2895_) == 8)
{
lean_object* v_declName_2902_; lean_object* v_type_2903_; lean_object* v_value_2904_; lean_object* v_body_2905_; uint8_t v_nondep_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_declName_2902_ = lean_ctor_get(v_e_2895_, 0);
lean_inc(v_declName_2902_);
v_type_2903_ = lean_ctor_get(v_e_2895_, 1);
lean_inc_ref(v_type_2903_);
v_value_2904_ = lean_ctor_get(v_e_2895_, 2);
lean_inc_ref(v_value_2904_);
v_body_2905_ = lean_ctor_get(v_e_2895_, 3);
lean_inc_ref(v_body_2905_);
v_nondep_2906_ = lean_ctor_get_uint8(v_e_2895_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2895_, 4);
v___x_2907_ = lean_expr_instantiate_rev(v_type_2903_, v_fvars_2894_);
lean_dec_ref(v_type_2903_);
lean_inc_ref(v_post_2890_);
lean_inc_ref(v_pre_2889_);
v___x_2908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2889_, v_post_2890_, v_usedLetOnly_2891_, v_skipConstInApp_2892_, v_skipInstances_2893_, v___x_2907_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v___x_2910_ = lean_expr_instantiate_rev(v_value_2904_, v_fvars_2894_);
lean_dec_ref(v_value_2904_);
lean_inc_ref(v_post_2890_);
lean_inc_ref(v_pre_2889_);
v___x_2911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2889_, v_post_2890_, v_usedLetOnly_2891_, v_skipConstInApp_2892_, v_skipInstances_2893_, v___x_2910_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___f_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = lean_box(v_usedLetOnly_2891_);
v___x_2914_ = lean_box(v_skipConstInApp_2892_);
v___x_2915_ = lean_box(v_skipInstances_2893_);
v___f_2916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2916_, 0, v_fvars_2894_);
lean_closure_set(v___f_2916_, 1, v_pre_2889_);
lean_closure_set(v___f_2916_, 2, v_post_2890_);
lean_closure_set(v___f_2916_, 3, v___x_2913_);
lean_closure_set(v___f_2916_, 4, v___x_2914_);
lean_closure_set(v___f_2916_, 5, v___x_2915_);
lean_closure_set(v___f_2916_, 6, v_body_2905_);
v___x_2917_ = 0;
v___x_2918_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2902_, v_a_2909_, v_a_2912_, v___f_2916_, v_nondep_2906_, v___x_2917_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2918_;
}
else
{
lean_dec(v_a_2909_);
lean_dec_ref(v_body_2905_);
lean_dec(v_declName_2902_);
lean_dec_ref(v_fvars_2894_);
lean_dec_ref(v_post_2890_);
lean_dec_ref(v_pre_2889_);
return v___x_2911_;
}
}
else
{
lean_dec_ref(v_body_2905_);
lean_dec_ref(v_value_2904_);
lean_dec(v_declName_2902_);
lean_dec_ref(v_fvars_2894_);
lean_dec_ref(v_post_2890_);
lean_dec_ref(v_pre_2889_);
return v___x_2908_;
}
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_expr_instantiate_rev(v_e_2895_, v_fvars_2894_);
lean_dec_ref(v_e_2895_);
lean_inc_ref(v_post_2890_);
lean_inc_ref(v_pre_2889_);
v___x_2920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2889_, v_post_2890_, v_usedLetOnly_2891_, v_skipConstInApp_2892_, v_skipInstances_2893_, v___x_2919_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; uint8_t v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = 0;
v___x_2923_ = 1;
v___x_2924_ = l_Lean_Meta_mkLetFVars(v_fvars_2894_, v_a_2921_, v_usedLetOnly_2891_, v___x_2922_, v___x_2923_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec_ref(v_fvars_2894_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2889_, v_post_2890_, v_usedLetOnly_2891_, v_skipConstInApp_2892_, v_skipInstances_2893_, v_a_2925_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2926_;
}
else
{
lean_dec_ref(v_post_2890_);
lean_dec_ref(v_pre_2889_);
return v___x_2924_;
}
}
else
{
lean_dec_ref(v_fvars_2894_);
lean_dec_ref(v_post_2890_);
lean_dec_ref(v_pre_2889_);
return v___x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2927_, lean_object* v_post_2928_, uint8_t v_usedLetOnly_2929_, uint8_t v_skipConstInApp_2930_, uint8_t v_skipInstances_2931_, size_t v_sz_2932_, size_t v_i_2933_, lean_object* v_bs_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_lt(v_i_2933_, v_sz_2932_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_dec_ref(v_post_2928_);
lean_dec_ref(v_pre_2927_);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v_bs_2934_);
return v___x_2942_;
}
else
{
lean_object* v_v_2943_; lean_object* v___x_2944_; 
v_v_2943_ = lean_array_uget_borrowed(v_bs_2934_, v_i_2933_);
lean_inc(v_v_2943_);
lean_inc_ref(v_post_2928_);
lean_inc_ref(v_pre_2927_);
v___x_2944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2927_, v_post_2928_, v_usedLetOnly_2929_, v_skipConstInApp_2930_, v_skipInstances_2931_, v_v_2943_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v_bs_x27_2947_; size_t v___x_2948_; size_t v___x_2949_; lean_object* v___x_2950_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v___x_2946_ = lean_unsigned_to_nat(0u);
v_bs_x27_2947_ = lean_array_uset(v_bs_2934_, v_i_2933_, v___x_2946_);
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2933_, v___x_2948_);
v___x_2950_ = lean_array_uset(v_bs_x27_2947_, v_i_2933_, v_a_2945_);
v_i_2933_ = v___x_2949_;
v_bs_2934_ = v___x_2950_;
goto _start;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v_bs_2934_);
lean_dec_ref(v_post_2928_);
lean_dec_ref(v_pre_2927_);
v_a_2952_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2944_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2944_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2960_, lean_object* v_post_2961_, uint8_t v_usedLetOnly_2962_, uint8_t v_skipConstInApp_2963_, uint8_t v_skipInstances_2964_, lean_object* v___x_2965_, lean_object* v___y_2966_, lean_object* v_b_2967_, lean_object* v_a_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2960_, v_post_2961_, v_usedLetOnly_2962_, v_skipConstInApp_2963_, v_skipInstances_2964_, v___x_2965_, v___y_2966_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2984_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2984_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2979_ = lean_array_fset(v_b_2967_, v_a_2968_, v_a_2975_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2980_);
v___x_2982_ = v___x_2977_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v_b_2967_);
v_a_2985_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2974_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2974_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_2993_, lean_object* v_post_2994_, lean_object* v_usedLetOnly_2995_, lean_object* v_skipConstInApp_2996_, lean_object* v_skipInstances_2997_, lean_object* v___x_2998_, lean_object* v___y_2999_, lean_object* v_b_3000_, lean_object* v_a_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
uint8_t v_usedLetOnly_boxed_3007_; uint8_t v_skipConstInApp_boxed_3008_; uint8_t v_skipInstances_boxed_3009_; lean_object* v_res_3010_; 
v_usedLetOnly_boxed_3007_ = lean_unbox(v_usedLetOnly_2995_);
v_skipConstInApp_boxed_3008_ = lean_unbox(v_skipConstInApp_2996_);
v_skipInstances_boxed_3009_ = lean_unbox(v_skipInstances_2997_);
v_res_3010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_2993_, v_post_2994_, v_usedLetOnly_boxed_3007_, v_skipConstInApp_boxed_3008_, v_skipInstances_boxed_3009_, v___x_2998_, v___y_2999_, v_b_3000_, v_a_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v_a_3001_);
lean_dec(v___y_2999_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3011_, lean_object* v___x_3012_, lean_object* v_pre_3013_, lean_object* v_post_3014_, uint8_t v_usedLetOnly_3015_, uint8_t v_skipConstInApp_3016_, uint8_t v_skipInstances_3017_, lean_object* v_a_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___y_3027_; uint8_t v___x_3050_; 
v___x_3050_ = lean_nat_dec_lt(v_a_3018_, v_upperBound_3011_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec(v_a_3018_);
lean_dec_ref(v_post_3014_);
lean_dec_ref(v_pre_3013_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_b_3019_);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = lean_array_fget_borrowed(v_b_3019_, v_a_3018_);
v___x_3053_ = lean_array_get_size(v___x_3012_);
v___x_3054_ = lean_nat_dec_lt(v_a_3018_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___f_3058_; 
lean_inc(v___x_3052_);
v___x_3055_ = lean_box(v_usedLetOnly_3015_);
v___x_3056_ = lean_box(v_skipConstInApp_3016_);
v___x_3057_ = lean_box(v_skipInstances_3017_);
lean_inc(v_a_3018_);
lean_inc(v___y_3020_);
lean_inc_ref(v_post_3014_);
lean_inc_ref(v_pre_3013_);
v___f_3058_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3058_, 0, v_pre_3013_);
lean_closure_set(v___f_3058_, 1, v_post_3014_);
lean_closure_set(v___f_3058_, 2, v___x_3055_);
lean_closure_set(v___f_3058_, 3, v___x_3056_);
lean_closure_set(v___f_3058_, 4, v___x_3057_);
lean_closure_set(v___f_3058_, 5, v___x_3052_);
lean_closure_set(v___f_3058_, 6, v___y_3020_);
lean_closure_set(v___f_3058_, 7, v_b_3019_);
lean_closure_set(v___f_3058_, 8, v_a_3018_);
v___y_3027_ = v___f_3058_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3059_; uint8_t v_isInstance_3060_; 
v___x_3059_ = lean_array_fget_borrowed(v___x_3012_, v_a_3018_);
v_isInstance_3060_ = lean_ctor_get_uint8(v___x_3059_, sizeof(void*)*1 + 4);
if (v_isInstance_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___f_3064_; 
lean_inc(v___x_3052_);
v___x_3061_ = lean_box(v_usedLetOnly_3015_);
v___x_3062_ = lean_box(v_skipConstInApp_3016_);
v___x_3063_ = lean_box(v_skipInstances_3017_);
lean_inc(v_a_3018_);
lean_inc(v___y_3020_);
lean_inc_ref(v_post_3014_);
lean_inc_ref(v_pre_3013_);
v___f_3064_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3064_, 0, v_pre_3013_);
lean_closure_set(v___f_3064_, 1, v_post_3014_);
lean_closure_set(v___f_3064_, 2, v___x_3061_);
lean_closure_set(v___f_3064_, 3, v___x_3062_);
lean_closure_set(v___f_3064_, 4, v___x_3063_);
lean_closure_set(v___f_3064_, 5, v___x_3052_);
lean_closure_set(v___f_3064_, 6, v___y_3020_);
lean_closure_set(v___f_3064_, 7, v_b_3019_);
lean_closure_set(v___f_3064_, 8, v_a_3018_);
v___y_3027_ = v___f_3064_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3065_; lean_object* v___f_3066_; 
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_b_3019_);
v___f_3066_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3066_, 0, v___x_3065_);
v___y_3027_ = v___f_3066_;
goto v___jp_3026_;
}
}
}
v___jp_3026_:
{
lean_object* v___x_3028_; 
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
v___x_3028_ = lean_apply_5(v___y_3027_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, lean_box(0));
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3041_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3041_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
if (lean_obj_tag(v_a_3029_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3035_; 
lean_dec(v_a_3018_);
lean_dec_ref(v_post_3014_);
lean_dec_ref(v_pre_3013_);
v_a_3033_ = lean_ctor_get(v_a_3029_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v_a_3029_, 1);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_a_3033_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_del_object(v___x_3031_);
v_a_3037_ = lean_ctor_get(v_a_3029_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v_a_3029_, 1);
v___x_3038_ = lean_unsigned_to_nat(1u);
v___x_3039_ = lean_nat_add(v_a_3018_, v___x_3038_);
lean_dec(v_a_3018_);
v_a_3018_ = v___x_3039_;
v_b_3019_ = v_a_3037_;
goto _start;
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_3018_);
lean_dec_ref(v_post_3014_);
lean_dec_ref(v_pre_3013_);
v_a_3042_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3028_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3028_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3067_, lean_object* v_pre_3068_, lean_object* v_post_3069_, uint8_t v_usedLetOnly_3070_, uint8_t v_skipConstInApp_3071_, lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_f_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; 
if (lean_obj_tag(v_x_3072_) == 5)
{
lean_object* v_fn_3130_; lean_object* v_arg_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_fn_3130_ = lean_ctor_get(v_x_3072_, 0);
lean_inc_ref(v_fn_3130_);
v_arg_3131_ = lean_ctor_get(v_x_3072_, 1);
lean_inc_ref(v_arg_3131_);
lean_dec_ref_known(v_x_3072_, 2);
v___x_3132_ = lean_array_set(v_x_3073_, v_x_3074_, v_arg_3131_);
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = lean_nat_sub(v_x_3074_, v___x_3133_);
lean_dec(v_x_3074_);
v_x_3072_ = v_fn_3130_;
v_x_3073_ = v___x_3132_;
v_x_3074_ = v___x_3134_;
goto _start;
}
else
{
lean_dec(v_x_3074_);
if (v_skipConstInApp_3071_ == 0)
{
goto v___jp_3127_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = l_Lean_Expr_isConst(v_x_3072_);
if (v___x_3136_ == 0)
{
goto v___jp_3127_;
}
else
{
v_f_3082_ = v_x_3072_;
v___y_3083_ = v___y_3075_;
v___y_3084_ = v___y_3076_;
v___y_3085_ = v___y_3077_;
v___y_3086_ = v___y_3078_;
v___y_3087_ = v___y_3079_;
goto v___jp_3081_;
}
}
}
v___jp_3081_:
{
if (v_skipInstances_3067_ == 0)
{
size_t v_sz_3088_; size_t v___x_3089_; lean_object* v___x_3090_; 
v_sz_3088_ = lean_array_size(v_x_3073_);
v___x_3089_ = ((size_t)0ULL);
lean_inc_ref(v_post_3069_);
lean_inc_ref(v_pre_3068_);
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3068_, v_post_3069_, v_usedLetOnly_3070_, v_skipConstInApp_3071_, v_skipInstances_3067_, v_sz_3088_, v___x_3089_, v_x_3073_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v___x_3092_ = l_Lean_mkAppN(v_f_3082_, v_a_3091_);
lean_dec(v_a_3091_);
v___x_3093_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3068_, v_post_3069_, v_usedLetOnly_3070_, v_skipConstInApp_3071_, v_skipInstances_3067_, v___x_3092_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
return v___x_3093_;
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_f_3082_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v_a_3094_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3090_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3090_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_array_get_size(v_x_3073_);
lean_inc_ref(v_f_3082_);
v___x_3103_ = l_Lean_Meta_getFunInfoNArgs(v_f_3082_, v___x_3102_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v_paramInfo_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v_paramInfo_3105_ = lean_ctor_get(v_a_3104_, 0);
lean_inc_ref(v_paramInfo_3105_);
lean_dec(v_a_3104_);
v___x_3106_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3069_);
lean_inc_ref(v_pre_3068_);
v___x_3107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3102_, v_paramInfo_3105_, v_pre_3068_, v_post_3069_, v_usedLetOnly_3070_, v_skipConstInApp_3071_, v_skipInstances_3067_, v___x_3106_, v_x_3073_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec_ref(v_paramInfo_3105_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v___x_3109_ = l_Lean_mkAppN(v_f_3082_, v_a_3108_);
lean_dec(v_a_3108_);
v___x_3110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3068_, v_post_3069_, v_usedLetOnly_3070_, v_skipConstInApp_3071_, v_skipInstances_3067_, v___x_3109_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
return v___x_3110_;
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v_f_3082_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v_a_3111_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3107_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_f_3082_);
lean_dec_ref(v_x_3073_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v_a_3119_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3103_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3103_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
v___jp_3127_:
{
lean_object* v___x_3128_; 
lean_inc_ref(v_post_3069_);
lean_inc_ref(v_pre_3068_);
v___x_3128_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3068_, v_post_3069_, v_usedLetOnly_3070_, v_skipConstInApp_3071_, v_skipInstances_3067_, v_x_3072_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v_f_3082_ = v_a_3129_;
v___y_3083_ = v___y_3075_;
v___y_3084_ = v___y_3076_;
v___y_3085_ = v___y_3077_;
v___y_3086_ = v___y_3078_;
v___y_3087_ = v___y_3079_;
goto v___jp_3081_;
}
else
{
lean_dec_ref(v_x_3073_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3137_, lean_object* v_pre_3138_, lean_object* v_e_3139_, lean_object* v_post_3140_, uint8_t v_usedLetOnly_3141_, uint8_t v_skipConstInApp_3142_, uint8_t v_skipInstances_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_Core_checkSystem(v___x_3137_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v___x_3151_; 
lean_dec_ref_known(v___x_3150_, 1);
lean_inc_ref(v_pre_3138_);
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc_ref(v_e_3139_);
v___x_3151_ = lean_apply_6(v_pre_3138_, v_e_3139_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3200_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3200_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3200_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___y_3157_; 
switch(lean_obj_tag(v_a_3152_))
{
case 0:
{
lean_object* v_e_3192_; lean_object* v___x_3194_; 
lean_dec_ref(v_post_3140_);
lean_dec_ref(v_e_3139_);
lean_dec_ref(v_pre_3138_);
v_e_3192_ = lean_ctor_get(v_a_3152_, 0);
lean_inc_ref(v_e_3192_);
lean_dec_ref_known(v_a_3152_, 1);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v_e_3192_);
v___x_3194_ = v___x_3154_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_e_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
case 1:
{
lean_object* v_e_3196_; lean_object* v___x_3197_; 
lean_del_object(v___x_3154_);
lean_dec_ref(v_e_3139_);
v_e_3196_ = lean_ctor_get(v_a_3152_, 0);
lean_inc_ref(v_e_3196_);
lean_dec_ref_known(v_a_3152_, 1);
v___x_3197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v_e_3196_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3197_;
}
default: 
{
lean_object* v_e_x3f_3198_; 
lean_del_object(v___x_3154_);
v_e_x3f_3198_ = lean_ctor_get(v_a_3152_, 0);
lean_inc(v_e_x3f_3198_);
lean_dec_ref_known(v_a_3152_, 1);
if (lean_obj_tag(v_e_x3f_3198_) == 0)
{
v___y_3157_ = v_e_3139_;
goto v___jp_3156_;
}
else
{
lean_object* v_val_3199_; 
lean_dec_ref(v_e_3139_);
v_val_3199_ = lean_ctor_get(v_e_x3f_3198_, 0);
lean_inc(v_val_3199_);
lean_dec_ref_known(v_e_x3f_3198_, 1);
v___y_3157_ = v_val_3199_;
goto v___jp_3156_;
}
}
}
v___jp_3156_:
{
switch(lean_obj_tag(v___y_3157_))
{
case 7:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___x_3158_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3159_;
}
case 6:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3161_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___x_3160_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3161_;
}
case 8:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3163_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___x_3162_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3163_;
}
case 5:
{
lean_object* v_dummy_3164_; lean_object* v_nargs_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_dummy_3164_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3165_ = l_Lean_Expr_getAppNumArgs(v___y_3157_);
lean_inc(v_nargs_3165_);
v___x_3166_ = lean_mk_array(v_nargs_3165_, v_dummy_3164_);
v___x_3167_ = lean_unsigned_to_nat(1u);
v___x_3168_ = lean_nat_sub(v_nargs_3165_, v___x_3167_);
lean_dec(v_nargs_3165_);
v___x_3169_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3143_, v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v___y_3157_, v___x_3166_, v___x_3168_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3169_;
}
case 10:
{
lean_object* v_data_3170_; lean_object* v_expr_3171_; lean_object* v___x_3172_; 
v_data_3170_ = lean_ctor_get(v___y_3157_, 0);
v_expr_3171_ = lean_ctor_get(v___y_3157_, 1);
lean_inc_ref(v_expr_3171_);
lean_inc_ref(v_post_3140_);
lean_inc_ref(v_pre_3138_);
v___x_3172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v_expr_3171_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; size_t v___x_3174_; size_t v___x_3175_; uint8_t v___x_3176_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = lean_ptr_addr(v_expr_3171_);
v___x_3175_ = lean_ptr_addr(v_a_3173_);
v___x_3176_ = lean_usize_dec_eq(v___x_3174_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_inc(v_data_3170_);
lean_dec_ref_known(v___y_3157_, 2);
v___x_3177_ = l_Lean_Expr_mdata___override(v_data_3170_, v_a_3173_);
v___x_3178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___x_3177_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; 
lean_dec(v_a_3173_);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3179_;
}
}
else
{
lean_dec_ref_known(v___y_3157_, 2);
lean_dec_ref(v_post_3140_);
lean_dec_ref(v_pre_3138_);
return v___x_3172_;
}
}
case 11:
{
lean_object* v_typeName_3180_; lean_object* v_idx_3181_; lean_object* v_struct_3182_; lean_object* v___x_3183_; 
v_typeName_3180_ = lean_ctor_get(v___y_3157_, 0);
v_idx_3181_ = lean_ctor_get(v___y_3157_, 1);
v_struct_3182_ = lean_ctor_get(v___y_3157_, 2);
lean_inc_ref(v_struct_3182_);
lean_inc_ref(v_post_3140_);
lean_inc_ref(v_pre_3138_);
v___x_3183_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v_struct_3182_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; size_t v___x_3185_; size_t v___x_3186_; uint8_t v___x_3187_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = lean_ptr_addr(v_struct_3182_);
v___x_3186_ = lean_ptr_addr(v_a_3184_);
v___x_3187_ = lean_usize_dec_eq(v___x_3185_, v___x_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_inc(v_idx_3181_);
lean_inc(v_typeName_3180_);
lean_dec_ref_known(v___y_3157_, 3);
v___x_3188_ = l_Lean_Expr_proj___override(v_typeName_3180_, v_idx_3181_, v_a_3184_);
v___x_3189_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___x_3188_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3189_;
}
else
{
lean_object* v___x_3190_; 
lean_dec(v_a_3184_);
v___x_3190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3190_;
}
}
else
{
lean_dec_ref_known(v___y_3157_, 3);
lean_dec_ref(v_post_3140_);
lean_dec_ref(v_pre_3138_);
return v___x_3183_;
}
}
default: 
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3138_, v_post_3140_, v_usedLetOnly_3141_, v_skipConstInApp_3142_, v_skipInstances_3143_, v___y_3157_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v_post_3140_);
lean_dec_ref(v_e_3139_);
lean_dec_ref(v_pre_3138_);
v_a_3201_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3151_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3151_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_post_3140_);
lean_dec_ref(v_e_3139_);
lean_dec_ref(v_pre_3138_);
v_a_3209_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3150_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3150_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3217_, lean_object* v_pre_3218_, lean_object* v_e_3219_, lean_object* v_post_3220_, lean_object* v_usedLetOnly_3221_, lean_object* v_skipConstInApp_3222_, lean_object* v_skipInstances_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
uint8_t v_usedLetOnly_boxed_3230_; uint8_t v_skipConstInApp_boxed_3231_; uint8_t v_skipInstances_boxed_3232_; lean_object* v_res_3233_; 
v_usedLetOnly_boxed_3230_ = lean_unbox(v_usedLetOnly_3221_);
v_skipConstInApp_boxed_3231_ = lean_unbox(v_skipConstInApp_3222_);
v_skipInstances_boxed_3232_ = lean_unbox(v_skipInstances_3223_);
v_res_3233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3217_, v_pre_3218_, v_e_3219_, v_post_3220_, v_usedLetOnly_boxed_3230_, v_skipConstInApp_boxed_3231_, v_skipInstances_boxed_3232_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3234_, lean_object* v_post_3235_, uint8_t v_usedLetOnly_3236_, uint8_t v_skipConstInApp_3237_, uint8_t v_skipInstances_3238_, lean_object* v_e_3239_, lean_object* v_a_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_inc(v_a_3240_);
v___x_3246_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3246_, 0, lean_box(0));
lean_closure_set(v___x_3246_, 1, lean_box(0));
lean_closure_set(v___x_3246_, 2, v_a_3240_);
v___x_3247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3246_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3282_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3282_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3282_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3248_, v_e_3239_);
lean_dec(v_a_3248_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; 
lean_del_object(v___x_3250_);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3254_ = lean_box(v_usedLetOnly_3236_);
v___x_3255_ = lean_box(v_skipConstInApp_3237_);
v___x_3256_ = lean_box(v_skipInstances_3238_);
lean_inc_ref(v_e_3239_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3257_, 0, v___x_3253_);
lean_closure_set(v___f_3257_, 1, v_pre_3234_);
lean_closure_set(v___f_3257_, 2, v_e_3239_);
lean_closure_set(v___f_3257_, 3, v_post_3235_);
lean_closure_set(v___f_3257_, 4, v___x_3254_);
lean_closure_set(v___f_3257_, 5, v___x_3255_);
lean_closure_set(v___f_3257_, 6, v___x_3256_);
v___x_3258_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3257_, v_a_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_n(v_a_3259_, 2);
lean_dec_ref_known(v___x_3258_, 1);
lean_inc(v_a_3240_);
v___f_3260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3260_, 0, v_a_3240_);
lean_closure_set(v___f_3260_, 1, v_e_3239_);
lean_closure_set(v___f_3260_, 2, v_a_3259_);
v___x_3261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3260_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v___x_3261_, 0);
lean_dec(v_unused_3269_);
v___x_3263_ = v___x_3261_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v___x_3261_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_a_3259_);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3259_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_a_3259_);
v_a_3270_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3261_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3261_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_dec_ref(v_e_3239_);
return v___x_3258_;
}
}
else
{
lean_object* v_val_3278_; lean_object* v___x_3280_; 
lean_dec_ref(v_e_3239_);
lean_dec_ref(v_post_3235_);
lean_dec_ref(v_pre_3234_);
v_val_3278_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_val_3278_);
lean_dec_ref_known(v___x_3252_, 1);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v_val_3278_);
v___x_3280_ = v___x_3250_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_val_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec_ref(v_e_3239_);
lean_dec_ref(v_post_3235_);
lean_dec_ref(v_pre_3234_);
v_a_3283_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3247_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3247_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3291_, lean_object* v_pre_3292_, lean_object* v_post_3293_, lean_object* v_usedLetOnly_3294_, lean_object* v_skipConstInApp_3295_, lean_object* v_skipInstances_3296_, lean_object* v_body_3297_, lean_object* v_x_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v_usedLetOnly_boxed_3305_; uint8_t v_skipConstInApp_boxed_3306_; uint8_t v_skipInstances_boxed_3307_; lean_object* v_res_3308_; 
v_usedLetOnly_boxed_3305_ = lean_unbox(v_usedLetOnly_3294_);
v_skipConstInApp_boxed_3306_ = lean_unbox(v_skipConstInApp_3295_);
v_skipInstances_boxed_3307_ = lean_unbox(v_skipInstances_3296_);
v_res_3308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3291_, v_pre_3292_, v_post_3293_, v_usedLetOnly_boxed_3305_, v_skipConstInApp_boxed_3306_, v_skipInstances_boxed_3307_, v_body_3297_, v_x_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3309_, lean_object* v_post_3310_, uint8_t v_usedLetOnly_3311_, uint8_t v_skipConstInApp_3312_, uint8_t v_skipInstances_3313_, lean_object* v_fvars_3314_, lean_object* v_e_3315_, lean_object* v_a_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
if (lean_obj_tag(v_e_3315_) == 7)
{
lean_object* v_binderName_3322_; lean_object* v_binderType_3323_; lean_object* v_body_3324_; uint8_t v_binderInfo_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_binderName_3322_ = lean_ctor_get(v_e_3315_, 0);
lean_inc(v_binderName_3322_);
v_binderType_3323_ = lean_ctor_get(v_e_3315_, 1);
lean_inc_ref(v_binderType_3323_);
v_body_3324_ = lean_ctor_get(v_e_3315_, 2);
lean_inc_ref(v_body_3324_);
v_binderInfo_3325_ = lean_ctor_get_uint8(v_e_3315_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3315_, 3);
v___x_3326_ = lean_expr_instantiate_rev(v_binderType_3323_, v_fvars_3314_);
lean_dec_ref(v_binderType_3323_);
lean_inc_ref(v_post_3310_);
lean_inc_ref(v_pre_3309_);
v___x_3327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3309_, v_post_3310_, v_usedLetOnly_3311_, v_skipConstInApp_3312_, v_skipInstances_3313_, v___x_3326_, v_a_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___f_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = lean_box(v_usedLetOnly_3311_);
v___x_3330_ = lean_box(v_skipConstInApp_3312_);
v___x_3331_ = lean_box(v_skipInstances_3313_);
v___f_3332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3332_, 0, v_fvars_3314_);
lean_closure_set(v___f_3332_, 1, v_pre_3309_);
lean_closure_set(v___f_3332_, 2, v_post_3310_);
lean_closure_set(v___f_3332_, 3, v___x_3329_);
lean_closure_set(v___f_3332_, 4, v___x_3330_);
lean_closure_set(v___f_3332_, 5, v___x_3331_);
lean_closure_set(v___f_3332_, 6, v_body_3324_);
v___x_3333_ = 0;
v___x_3334_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3322_, v_binderInfo_3325_, v_a_3328_, v___f_3332_, v___x_3333_, v_a_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3334_;
}
else
{
lean_dec_ref(v_body_3324_);
lean_dec(v_binderName_3322_);
lean_dec_ref(v_fvars_3314_);
lean_dec_ref(v_post_3310_);
lean_dec_ref(v_pre_3309_);
return v___x_3327_;
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_expr_instantiate_rev(v_e_3315_, v_fvars_3314_);
lean_dec_ref(v_e_3315_);
lean_inc_ref(v_post_3310_);
lean_inc_ref(v_pre_3309_);
v___x_3336_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3309_, v_post_3310_, v_usedLetOnly_3311_, v_skipConstInApp_3312_, v_skipInstances_3313_, v___x_3335_, v_a_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; uint8_t v___x_3338_; uint8_t v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v___x_3338_ = 0;
v___x_3339_ = 1;
v___x_3340_ = 1;
v___x_3341_ = l_Lean_Meta_mkForallFVars(v_fvars_3314_, v_a_3337_, v___x_3338_, v_usedLetOnly_3311_, v___x_3339_, v___x_3340_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec_ref(v_fvars_3314_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3309_, v_post_3310_, v_usedLetOnly_3311_, v_skipConstInApp_3312_, v_skipInstances_3313_, v_a_3342_, v_a_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3343_;
}
else
{
lean_dec_ref(v_post_3310_);
lean_dec_ref(v_pre_3309_);
return v___x_3341_;
}
}
else
{
lean_dec_ref(v_fvars_3314_);
lean_dec_ref(v_post_3310_);
lean_dec_ref(v_pre_3309_);
return v___x_3336_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3344_, lean_object* v_pre_3345_, lean_object* v_post_3346_, uint8_t v_usedLetOnly_3347_, uint8_t v_skipConstInApp_3348_, uint8_t v_skipInstances_3349_, lean_object* v_body_3350_, lean_object* v_x_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_array_push(v_fvars_3344_, v_x_3351_);
v___x_3359_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3345_, v_post_3346_, v_usedLetOnly_3347_, v_skipConstInApp_3348_, v_skipInstances_3349_, v___x_3358_, v_body_3350_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3360_, lean_object* v_post_3361_, lean_object* v_usedLetOnly_3362_, lean_object* v_skipConstInApp_3363_, lean_object* v_skipInstances_3364_, lean_object* v_e_3365_, lean_object* v_a_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
uint8_t v_usedLetOnly_boxed_3372_; uint8_t v_skipConstInApp_boxed_3373_; uint8_t v_skipInstances_boxed_3374_; lean_object* v_res_3375_; 
v_usedLetOnly_boxed_3372_ = lean_unbox(v_usedLetOnly_3362_);
v_skipConstInApp_boxed_3373_ = lean_unbox(v_skipConstInApp_3363_);
v_skipInstances_boxed_3374_ = lean_unbox(v_skipInstances_3364_);
v_res_3375_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3360_, v_post_3361_, v_usedLetOnly_boxed_3372_, v_skipConstInApp_boxed_3373_, v_skipInstances_boxed_3374_, v_e_3365_, v_a_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v_a_3366_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3376_, lean_object* v_post_3377_, lean_object* v_usedLetOnly_3378_, lean_object* v_skipConstInApp_3379_, lean_object* v_skipInstances_3380_, lean_object* v_sz_3381_, lean_object* v_i_3382_, lean_object* v_bs_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v_usedLetOnly_boxed_3390_; uint8_t v_skipConstInApp_boxed_3391_; uint8_t v_skipInstances_boxed_3392_; size_t v_sz_boxed_3393_; size_t v_i_boxed_3394_; lean_object* v_res_3395_; 
v_usedLetOnly_boxed_3390_ = lean_unbox(v_usedLetOnly_3378_);
v_skipConstInApp_boxed_3391_ = lean_unbox(v_skipConstInApp_3379_);
v_skipInstances_boxed_3392_ = lean_unbox(v_skipInstances_3380_);
v_sz_boxed_3393_ = lean_unbox_usize(v_sz_3381_);
lean_dec(v_sz_3381_);
v_i_boxed_3394_ = lean_unbox_usize(v_i_3382_);
lean_dec(v_i_3382_);
v_res_3395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3376_, v_post_3377_, v_usedLetOnly_boxed_3390_, v_skipConstInApp_boxed_3391_, v_skipInstances_boxed_3392_, v_sz_boxed_3393_, v_i_boxed_3394_, v_bs_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3396_, lean_object* v_post_3397_, lean_object* v_usedLetOnly_3398_, lean_object* v_skipConstInApp_3399_, lean_object* v_skipInstances_3400_, lean_object* v_e_3401_, lean_object* v_a_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v_usedLetOnly_boxed_3408_; uint8_t v_skipConstInApp_boxed_3409_; uint8_t v_skipInstances_boxed_3410_; lean_object* v_res_3411_; 
v_usedLetOnly_boxed_3408_ = lean_unbox(v_usedLetOnly_3398_);
v_skipConstInApp_boxed_3409_ = lean_unbox(v_skipConstInApp_3399_);
v_skipInstances_boxed_3410_ = lean_unbox(v_skipInstances_3400_);
v_res_3411_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3396_, v_post_3397_, v_usedLetOnly_boxed_3408_, v_skipConstInApp_boxed_3409_, v_skipInstances_boxed_3410_, v_e_3401_, v_a_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_a_3402_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3412_, lean_object* v_post_3413_, lean_object* v_usedLetOnly_3414_, lean_object* v_skipConstInApp_3415_, lean_object* v_skipInstances_3416_, lean_object* v_fvars_3417_, lean_object* v_e_3418_, lean_object* v_a_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v_usedLetOnly_boxed_3425_; uint8_t v_skipConstInApp_boxed_3426_; uint8_t v_skipInstances_boxed_3427_; lean_object* v_res_3428_; 
v_usedLetOnly_boxed_3425_ = lean_unbox(v_usedLetOnly_3414_);
v_skipConstInApp_boxed_3426_ = lean_unbox(v_skipConstInApp_3415_);
v_skipInstances_boxed_3427_ = lean_unbox(v_skipInstances_3416_);
v_res_3428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3412_, v_post_3413_, v_usedLetOnly_boxed_3425_, v_skipConstInApp_boxed_3426_, v_skipInstances_boxed_3427_, v_fvars_3417_, v_e_3418_, v_a_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v_a_3419_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3429_, lean_object* v_post_3430_, lean_object* v_usedLetOnly_3431_, lean_object* v_skipConstInApp_3432_, lean_object* v_skipInstances_3433_, lean_object* v_fvars_3434_, lean_object* v_e_3435_, lean_object* v_a_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v_usedLetOnly_boxed_3442_; uint8_t v_skipConstInApp_boxed_3443_; uint8_t v_skipInstances_boxed_3444_; lean_object* v_res_3445_; 
v_usedLetOnly_boxed_3442_ = lean_unbox(v_usedLetOnly_3431_);
v_skipConstInApp_boxed_3443_ = lean_unbox(v_skipConstInApp_3432_);
v_skipInstances_boxed_3444_ = lean_unbox(v_skipInstances_3433_);
v_res_3445_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3429_, v_post_3430_, v_usedLetOnly_boxed_3442_, v_skipConstInApp_boxed_3443_, v_skipInstances_boxed_3444_, v_fvars_3434_, v_e_3435_, v_a_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v_a_3436_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3446_, lean_object* v_post_3447_, lean_object* v_usedLetOnly_3448_, lean_object* v_skipConstInApp_3449_, lean_object* v_skipInstances_3450_, lean_object* v_fvars_3451_, lean_object* v_e_3452_, lean_object* v_a_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
uint8_t v_usedLetOnly_boxed_3459_; uint8_t v_skipConstInApp_boxed_3460_; uint8_t v_skipInstances_boxed_3461_; lean_object* v_res_3462_; 
v_usedLetOnly_boxed_3459_ = lean_unbox(v_usedLetOnly_3448_);
v_skipConstInApp_boxed_3460_ = lean_unbox(v_skipConstInApp_3449_);
v_skipInstances_boxed_3461_ = lean_unbox(v_skipInstances_3450_);
v_res_3462_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3446_, v_post_3447_, v_usedLetOnly_boxed_3459_, v_skipConstInApp_boxed_3460_, v_skipInstances_boxed_3461_, v_fvars_3451_, v_e_3452_, v_a_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v_a_3453_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3463_, lean_object* v___x_3464_, lean_object* v_pre_3465_, lean_object* v_post_3466_, lean_object* v_usedLetOnly_3467_, lean_object* v_skipConstInApp_3468_, lean_object* v_skipInstances_3469_, lean_object* v_a_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v_usedLetOnly_boxed_3478_; uint8_t v_skipConstInApp_boxed_3479_; uint8_t v_skipInstances_boxed_3480_; lean_object* v_res_3481_; 
v_usedLetOnly_boxed_3478_ = lean_unbox(v_usedLetOnly_3467_);
v_skipConstInApp_boxed_3479_ = lean_unbox(v_skipConstInApp_3468_);
v_skipInstances_boxed_3480_ = lean_unbox(v_skipInstances_3469_);
v_res_3481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3463_, v___x_3464_, v_pre_3465_, v_post_3466_, v_usedLetOnly_boxed_3478_, v_skipConstInApp_boxed_3479_, v_skipInstances_boxed_3480_, v_a_3470_, v_b_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___x_3464_);
lean_dec(v_upperBound_3463_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3482_, lean_object* v_pre_3483_, lean_object* v_post_3484_, lean_object* v_usedLetOnly_3485_, lean_object* v_skipConstInApp_3486_, lean_object* v_x_3487_, lean_object* v_x_3488_, lean_object* v_x_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v_skipInstances_boxed_3496_; uint8_t v_usedLetOnly_boxed_3497_; uint8_t v_skipConstInApp_boxed_3498_; lean_object* v_res_3499_; 
v_skipInstances_boxed_3496_ = lean_unbox(v_skipInstances_3482_);
v_usedLetOnly_boxed_3497_ = lean_unbox(v_usedLetOnly_3485_);
v_skipConstInApp_boxed_3498_ = lean_unbox(v_skipConstInApp_3486_);
v_res_3499_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3496_, v_pre_3483_, v_post_3484_, v_usedLetOnly_boxed_3497_, v_skipConstInApp_boxed_3498_, v_x_3487_, v_x_3488_, v_x_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
return v_res_3499_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_unsigned_to_nat(16u);
v___x_3502_ = lean_mk_array(v___x_3501_, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3504_ = lean_unsigned_to_nat(0u);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3503_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3507_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3507_, 0, lean_box(0));
lean_closure_set(v___x_3507_, 1, lean_box(0));
lean_closure_set(v___x_3507_, 2, v___x_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3508_, lean_object* v_pre_3509_, lean_object* v_post_3510_, uint8_t v_usedLetOnly_3511_, uint8_t v_skipConstInApp_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v_a_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; 
v___x_3518_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3519_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3518_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v___x_3521_ = 0;
v___x_3522_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3509_, v_post_3510_, v_usedLetOnly_3511_, v_skipConstInApp_3512_, v___x_3521_, v_input_3508_, v_a_3520_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3524_, 0, lean_box(0));
lean_closure_set(v___x_3524_, 1, lean_box(0));
lean_closure_set(v___x_3524_, 2, v_a_3520_);
v___x_3525_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3524_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v___x_3525_, 0);
lean_dec(v_unused_3533_);
v___x_3527_ = v___x_3525_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v___x_3525_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v_a_3523_);
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3523_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_dec(v_a_3520_);
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3534_, lean_object* v_pre_3535_, lean_object* v_post_3536_, lean_object* v_usedLetOnly_3537_, lean_object* v_skipConstInApp_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
uint8_t v_usedLetOnly_boxed_3544_; uint8_t v_skipConstInApp_boxed_3545_; lean_object* v_res_3546_; 
v_usedLetOnly_boxed_3544_ = lean_unbox(v_usedLetOnly_3537_);
v_skipConstInApp_boxed_3545_ = lean_unbox(v_skipConstInApp_3538_);
v_res_3546_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3534_, v_pre_3535_, v_post_3536_, v_usedLetOnly_boxed_3544_, v_skipConstInApp_boxed_3545_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3548_, lean_object* v_p_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v___x_3555_; lean_object* v_a_3556_; lean_object* v___f_3557_; lean_object* v___f_3558_; uint8_t v___x_3559_; lean_object* v___x_3560_; 
v___x_3555_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3548_, v_a_3551_);
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
v___f_3557_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3558_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3558_, 0, v_p_3549_);
v___x_3559_ = 0;
v___x_3560_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3556_, v___f_3557_, v___f_3558_, v___x_3559_, v___x_3559_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3561_, lean_object* v_p_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_Meta_etaStructReduce(v_e_3561_, v_p_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3569_, lean_object* v___x_3570_, lean_object* v_pre_3571_, lean_object* v_post_3572_, uint8_t v_usedLetOnly_3573_, uint8_t v_skipConstInApp_3574_, uint8_t v_skipInstances_3575_, lean_object* v___x_3576_, lean_object* v_inst_3577_, lean_object* v_R_3578_, lean_object* v_a_3579_, lean_object* v_b_3580_, lean_object* v_c_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3569_, v___x_3570_, v_pre_3571_, v_post_3572_, v_usedLetOnly_3573_, v_skipConstInApp_3574_, v_skipInstances_3575_, v_a_3579_, v_b_3580_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3589_ = _args[0];
lean_object* v___x_3590_ = _args[1];
lean_object* v_pre_3591_ = _args[2];
lean_object* v_post_3592_ = _args[3];
lean_object* v_usedLetOnly_3593_ = _args[4];
lean_object* v_skipConstInApp_3594_ = _args[5];
lean_object* v_skipInstances_3595_ = _args[6];
lean_object* v___x_3596_ = _args[7];
lean_object* v_inst_3597_ = _args[8];
lean_object* v_R_3598_ = _args[9];
lean_object* v_a_3599_ = _args[10];
lean_object* v_b_3600_ = _args[11];
lean_object* v_c_3601_ = _args[12];
lean_object* v___y_3602_ = _args[13];
lean_object* v___y_3603_ = _args[14];
lean_object* v___y_3604_ = _args[15];
lean_object* v___y_3605_ = _args[16];
lean_object* v___y_3606_ = _args[17];
lean_object* v___y_3607_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3608_; uint8_t v_skipConstInApp_boxed_3609_; uint8_t v_skipInstances_boxed_3610_; lean_object* v_res_3611_; 
v_usedLetOnly_boxed_3608_ = lean_unbox(v_usedLetOnly_3593_);
v_skipConstInApp_boxed_3609_ = lean_unbox(v_skipConstInApp_3594_);
v_skipInstances_boxed_3610_ = lean_unbox(v_skipInstances_3595_);
v_res_3611_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3589_, v___x_3590_, v_pre_3591_, v_post_3592_, v_usedLetOnly_boxed_3608_, v_skipConstInApp_boxed_3609_, v_skipInstances_boxed_3610_, v___x_3596_, v_inst_3597_, v_R_3598_, v_a_3599_, v_b_3600_, v_c_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec(v___x_3596_);
lean_dec_ref(v___x_3590_);
lean_dec(v_upperBound_3589_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3612_, lean_object* v_m_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3613_, v_a_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3616_, v_m_3617_, v_a_3618_);
lean_dec_ref(v_a_3618_);
lean_dec_ref(v_m_3617_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3620_, lean_object* v_name_3621_, uint8_t v_bi_3622_, lean_object* v_type_3623_, lean_object* v_k_3624_, uint8_t v_kind_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3621_, v_bi_3622_, v_type_3623_, v_k_3624_, v_kind_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3633_, lean_object* v_name_3634_, lean_object* v_bi_3635_, lean_object* v_type_3636_, lean_object* v_k_3637_, lean_object* v_kind_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
uint8_t v_bi_boxed_3645_; uint8_t v_kind_boxed_3646_; lean_object* v_res_3647_; 
v_bi_boxed_3645_ = lean_unbox(v_bi_3635_);
v_kind_boxed_3646_ = lean_unbox(v_kind_3638_);
v_res_3647_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3633_, v_name_3634_, v_bi_boxed_3645_, v_type_3636_, v_k_3637_, v_kind_boxed_3646_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3648_, lean_object* v_name_3649_, lean_object* v_type_3650_, lean_object* v_val_3651_, lean_object* v_k_3652_, uint8_t v_nondep_3653_, uint8_t v_kind_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3649_, v_type_3650_, v_val_3651_, v_k_3652_, v_nondep_3653_, v_kind_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3662_, lean_object* v_name_3663_, lean_object* v_type_3664_, lean_object* v_val_3665_, lean_object* v_k_3666_, lean_object* v_nondep_3667_, lean_object* v_kind_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
uint8_t v_nondep_boxed_3675_; uint8_t v_kind_boxed_3676_; lean_object* v_res_3677_; 
v_nondep_boxed_3675_ = lean_unbox(v_nondep_3667_);
v_kind_boxed_3676_ = lean_unbox(v_kind_3668_);
v_res_3677_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3662_, v_name_3663_, v_type_3664_, v_val_3665_, v_k_3666_, v_nondep_boxed_3675_, v_kind_boxed_3676_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3678_, lean_object* v_ref_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3679_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3686_, lean_object* v_ref_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3686_, v_ref_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3694_, lean_object* v_x_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3703_, v_x_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3712_, lean_object* v_m_3713_, lean_object* v_a_3714_, lean_object* v_b_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3713_, v_a_3714_, v_b_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3717_, lean_object* v_a_3718_, lean_object* v_x_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3718_, v_x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3721_, lean_object* v_a_3722_, lean_object* v_x_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3721_, v_a_3722_, v_x_3723_);
lean_dec(v_x_3723_);
lean_dec_ref(v_a_3722_);
return v_res_3724_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3725_, lean_object* v_a_3726_, lean_object* v_x_3727_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3726_, v_x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3729_, lean_object* v_a_3730_, lean_object* v_x_3731_){
_start:
{
uint8_t v_res_3732_; lean_object* v_r_3733_; 
v_res_3732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3729_, v_a_3730_, v_x_3731_);
lean_dec(v_x_3731_);
lean_dec_ref(v_a_3730_);
v_r_3733_ = lean_box(v_res_3732_);
return v_r_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3734_, lean_object* v_data_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3737_, lean_object* v_a_3738_, lean_object* v_b_3739_, lean_object* v_x_3740_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3738_, v_b_3739_, v_x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3742_, lean_object* v_i_3743_, lean_object* v_source_3744_, lean_object* v_target_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3743_, v_source_3744_, v_target_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3747_, lean_object* v_x_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3748_, v_x_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3751_, lean_object* v_inst_3752_, lean_object* v_toBind_3753_, lean_object* v___f_3754_, lean_object* v_____do__lift_3755_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3756_, 0, v_____do__lift_3755_);
lean_closure_set(v___x_3756_, 1, v_binderType_3751_);
v___x_3757_ = lean_apply_2(v_inst_3752_, lean_box(0), v___x_3756_);
v___x_3758_ = lean_apply_4(v_toBind_3753_, lean_box(0), lean_box(0), v___x_3757_, v___f_3754_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3759_, lean_object* v_usedFields_3760_, lean_object* v_binderName_3761_, lean_object* v_body_3762_, lean_object* v_val_3763_, lean_object* v_inst_3764_, lean_object* v_inst_3765_, lean_object* v_fieldVal_x3f_3766_, lean_object* v_____do__lift_3767_){
_start:
{
uint8_t v_____do__lift_289__boxed_3768_; lean_object* v_res_3769_; 
v_____do__lift_289__boxed_3768_ = lean_unbox(v_____do__lift_3767_);
v_res_3769_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3759_, v_usedFields_3760_, v_binderName_3761_, v_body_3762_, v_val_3763_, v_inst_3764_, v_inst_3765_, v_fieldVal_x3f_3766_, v_____do__lift_289__boxed_3768_);
lean_dec_ref(v_val_3763_);
lean_dec_ref(v_body_3762_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3770_, lean_object* v_usedFields_3771_, lean_object* v_binderName_3772_, lean_object* v_body_3773_, lean_object* v_inst_3774_, lean_object* v_inst_3775_, lean_object* v_fieldVal_x3f_3776_, lean_object* v_binderType_3777_, lean_object* v_toBind_3778_, lean_object* v_____x_3779_){
_start:
{
if (lean_obj_tag(v_____x_3779_) == 1)
{
lean_object* v_val_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_val_3780_ = lean_ctor_get(v_____x_3779_, 0);
lean_inc_n(v_val_3780_, 2);
lean_dec_ref_known(v_____x_3779_, 1);
lean_inc_n(v_inst_3775_, 2);
v___f_3781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3781_, 0, v_toPure_3770_);
lean_closure_set(v___f_3781_, 1, v_usedFields_3771_);
lean_closure_set(v___f_3781_, 2, v_binderName_3772_);
lean_closure_set(v___f_3781_, 3, v_body_3773_);
lean_closure_set(v___f_3781_, 4, v_val_3780_);
lean_closure_set(v___f_3781_, 5, v_inst_3774_);
lean_closure_set(v___f_3781_, 6, v_inst_3775_);
lean_closure_set(v___f_3781_, 7, v_fieldVal_x3f_3776_);
lean_inc(v_toBind_3778_);
v___f_3782_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3782_, 0, v_binderType_3777_);
lean_closure_set(v___f_3782_, 1, v_inst_3775_);
lean_closure_set(v___f_3782_, 2, v_toBind_3778_);
lean_closure_set(v___f_3782_, 3, v___f_3781_);
v___x_3783_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3783_, 0, v_val_3780_);
v___x_3784_ = lean_apply_2(v_inst_3775_, lean_box(0), v___x_3783_);
v___x_3785_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v___x_3784_, v___f_3782_);
return v___x_3785_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec(v_____x_3779_);
lean_dec(v_toBind_3778_);
lean_dec_ref(v_binderType_3777_);
lean_dec(v_fieldVal_x3f_3776_);
lean_dec(v_inst_3775_);
lean_dec_ref(v_inst_3774_);
lean_dec_ref(v_body_3773_);
lean_dec(v_binderName_3772_);
lean_dec(v_usedFields_3771_);
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_apply_2(v_toPure_3770_, lean_box(0), v___x_3786_);
return v___x_3787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3791_, lean_object* v_inst_3792_, lean_object* v_fieldVal_x3f_3793_, lean_object* v_usedFields_3794_, lean_object* v_e_3795_){
_start:
{
lean_object* v_toApplicative_3796_; lean_object* v_toBind_3797_; lean_object* v_toPure_3798_; 
v_toApplicative_3796_ = lean_ctor_get(v_inst_3791_, 0);
v_toBind_3797_ = lean_ctor_get(v_inst_3791_, 1);
v_toPure_3798_ = lean_ctor_get(v_toApplicative_3796_, 1);
lean_inc(v_toPure_3798_);
if (lean_obj_tag(v_e_3795_) == 6)
{
lean_object* v_binderName_3803_; lean_object* v_binderType_3804_; lean_object* v_body_3805_; lean_object* v___f_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_inc_n(v_toBind_3797_, 2);
v_binderName_3803_ = lean_ctor_get(v_e_3795_, 0);
lean_inc_n(v_binderName_3803_, 2);
v_binderType_3804_ = lean_ctor_get(v_e_3795_, 1);
lean_inc_ref(v_binderType_3804_);
v_body_3805_ = lean_ctor_get(v_e_3795_, 2);
lean_inc_ref(v_body_3805_);
lean_dec_ref_known(v_e_3795_, 3);
lean_inc(v_fieldVal_x3f_3793_);
v___f_3806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3806_, 0, v_toPure_3798_);
lean_closure_set(v___f_3806_, 1, v_usedFields_3794_);
lean_closure_set(v___f_3806_, 2, v_binderName_3803_);
lean_closure_set(v___f_3806_, 3, v_body_3805_);
lean_closure_set(v___f_3806_, 4, v_inst_3791_);
lean_closure_set(v___f_3806_, 5, v_inst_3792_);
lean_closure_set(v___f_3806_, 6, v_fieldVal_x3f_3793_);
lean_closure_set(v___f_3806_, 7, v_binderType_3804_);
lean_closure_set(v___f_3806_, 8, v_toBind_3797_);
v___x_3807_ = lean_apply_1(v_fieldVal_x3f_3793_, v_binderName_3803_);
v___x_3808_ = lean_apply_4(v_toBind_3797_, lean_box(0), lean_box(0), v___x_3807_, v___f_3806_);
return v___x_3808_;
}
else
{
lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_fieldVal_x3f_3793_);
lean_dec(v_inst_3792_);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_inst_3791_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; 
v_unused_3826_ = lean_ctor_get(v_inst_3791_, 1);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_inst_3791_, 0);
lean_dec(v_unused_3827_);
v___x_3810_ = v_inst_3791_;
v_isShared_3811_ = v_isSharedCheck_3825_;
goto v_resetjp_3809_;
}
else
{
lean_dec(v_inst_3791_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3825_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3812_; uint8_t v___x_3813_; 
lean_inc_ref(v_e_3795_);
v___x_3812_ = l_Lean_Expr_cleanupAnnotations(v_e_3795_);
v___x_3813_ = l_Lean_Expr_isApp(v___x_3812_);
if (v___x_3813_ == 0)
{
lean_dec_ref(v___x_3812_);
lean_del_object(v___x_3810_);
goto v___jp_3799_;
}
else
{
lean_object* v_arg_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_arg_3814_ = lean_ctor_get(v___x_3812_, 1);
lean_inc_ref(v_arg_3814_);
v___x_3815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3812_);
v___x_3816_ = l_Lean_Expr_isApp(v___x_3815_);
if (v___x_3816_ == 0)
{
lean_dec_ref(v___x_3815_);
lean_dec_ref(v_arg_3814_);
lean_del_object(v___x_3810_);
goto v___jp_3799_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3815_);
v___x_3818_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3819_ = l_Lean_Expr_isConstOf(v___x_3817_, v___x_3818_);
lean_dec_ref(v___x_3817_);
if (v___x_3819_ == 0)
{
lean_dec_ref(v_arg_3814_);
lean_del_object(v___x_3810_);
goto v___jp_3799_;
}
else
{
lean_object* v___x_3821_; 
lean_dec_ref(v_e_3795_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 1, v_arg_3814_);
lean_ctor_set(v___x_3810_, 0, v_usedFields_3794_);
v___x_3821_ = v___x_3810_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_usedFields_3794_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_arg_3814_);
v___x_3821_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
v___x_3823_ = lean_apply_2(v_toPure_3798_, lean_box(0), v___x_3822_);
return v___x_3823_;
}
}
}
}
}
}
v___jp_3799_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v_usedFields_3794_);
lean_ctor_set(v___x_3800_, 1, v_e_3795_);
v___x_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
v___x_3802_ = lean_apply_2(v_toPure_3798_, lean_box(0), v___x_3801_);
return v___x_3802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3828_, lean_object* v_usedFields_3829_, lean_object* v_binderName_3830_, lean_object* v_body_3831_, lean_object* v_val_3832_, lean_object* v_inst_3833_, lean_object* v_inst_3834_, lean_object* v_fieldVal_x3f_3835_, uint8_t v_____do__lift_3836_){
_start:
{
if (v_____do__lift_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec(v_fieldVal_x3f_3835_);
lean_dec(v_inst_3834_);
lean_dec_ref(v_inst_3833_);
lean_dec(v_binderName_3830_);
lean_dec(v_usedFields_3829_);
v___x_3837_ = lean_box(0);
v___x_3838_ = lean_apply_2(v_toPure_3828_, lean_box(0), v___x_3837_);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_toPure_3828_);
v___x_3839_ = l_Lean_NameSet_insert(v_usedFields_3829_, v_binderName_3830_);
v___x_3840_ = lean_expr_instantiate1(v_body_3831_, v_val_3832_);
v___x_3841_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3833_, v_inst_3834_, v_fieldVal_x3f_3835_, v___x_3839_, v___x_3840_);
return v___x_3841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3842_, lean_object* v_inst_3843_, lean_object* v_inst_3844_, lean_object* v_fieldVal_x3f_3845_, lean_object* v_usedFields_3846_, lean_object* v_e_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3843_, v_inst_3844_, v_fieldVal_x3f_3845_, v_usedFields_3846_, v_e_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3849_, lean_object* v_inst_3850_, lean_object* v_fieldVal_x3f_3851_, lean_object* v_toPure_3852_, lean_object* v_____s_3853_){
_start:
{
lean_object* v_fst_3854_; 
v_fst_3854_ = lean_ctor_get(v_____s_3853_, 0);
if (lean_obj_tag(v_fst_3854_) == 0)
{
lean_object* v_snd_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec(v_toPure_3852_);
v_snd_3855_ = lean_ctor_get(v_____s_3853_, 1);
lean_inc(v_snd_3855_);
lean_dec_ref(v_____s_3853_);
v___x_3856_ = l_Lean_NameSet_empty;
v___x_3857_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3849_, v_inst_3850_, v_fieldVal_x3f_3851_, v___x_3856_, v_snd_3855_);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; lean_object* v___x_3859_; 
lean_inc_ref(v_fst_3854_);
lean_dec_ref(v_____s_3853_);
lean_dec(v_fieldVal_x3f_3851_);
lean_dec(v_inst_3850_);
lean_dec_ref(v_inst_3849_);
v_val_3858_ = lean_ctor_get(v_fst_3854_, 0);
lean_inc(v_val_3858_);
lean_dec_ref_known(v_fst_3854_, 1);
v___x_3859_ = lean_apply_2(v_toPure_3852_, lean_box(0), v_val_3858_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3860_, lean_object* v_a_3861_, lean_object* v___x_3862_, lean_object* v_toPure_3863_, lean_object* v_____r_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3865_ = lean_expr_instantiate1(v_body_3860_, v_a_3861_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3862_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
v___x_3868_ = lean_apply_2(v_toPure_3863_, lean_box(0), v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3869_, lean_object* v_a_3870_, lean_object* v___x_3871_, lean_object* v_toPure_3872_, lean_object* v_____r_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3869_, v_a_3870_, v___x_3871_, v_toPure_3872_, v_____r_3873_);
lean_dec_ref(v_a_3870_);
lean_dec_ref(v_body_3869_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3877_, lean_object* v_toPure_3878_, lean_object* v___f_3879_, uint8_t v_____do__lift_3880_){
_start:
{
if (v_____do__lift_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_dec(v___f_3879_);
v___x_3881_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v_snd_3877_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
v___x_3884_ = lean_apply_2(v_toPure_3878_, lean_box(0), v___x_3883_);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec(v_toPure_3878_);
lean_dec(v_snd_3877_);
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_apply_1(v___f_3879_, v___x_3885_);
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3887_, lean_object* v_toPure_3888_, lean_object* v___f_3889_, lean_object* v_____do__lift_3890_){
_start:
{
uint8_t v_____do__lift_560__boxed_3891_; lean_object* v_res_3892_; 
v_____do__lift_560__boxed_3891_ = lean_unbox(v_____do__lift_3890_);
v_res_3892_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3887_, v_toPure_3888_, v___f_3889_, v_____do__lift_560__boxed_3891_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3893_, lean_object* v_inst_3894_, lean_object* v_toBind_3895_, lean_object* v___f_3896_, lean_object* v_____do__lift_3897_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3898_, 0, v_____do__lift_3897_);
lean_closure_set(v___x_3898_, 1, v_binderType_3893_);
v___x_3899_ = lean_apply_2(v_inst_3894_, lean_box(0), v___x_3898_);
v___x_3900_ = lean_apply_4(v_toBind_3895_, lean_box(0), lean_box(0), v___x_3899_, v___f_3896_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3901_, lean_object* v_toPure_3902_, lean_object* v_levels_x3f_3903_, lean_object* v_inst_3904_, lean_object* v_toBind_3905_, lean_object* v_a_3906_, lean_object* v_x_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_snd_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3929_; 
v_snd_3909_ = lean_ctor_get(v___y_3908_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___y_3908_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v___y_3908_, 0);
lean_dec(v_unused_3930_);
v___x_3911_ = v___y_3908_;
v_isShared_3912_ = v_isSharedCheck_3929_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_snd_3909_);
lean_dec(v___y_3908_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3929_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
if (lean_obj_tag(v_snd_3909_) == 6)
{
lean_object* v_binderType_3913_; lean_object* v_body_3914_; lean_object* v___f_3915_; 
lean_del_object(v___x_3911_);
v_binderType_3913_ = lean_ctor_get(v_snd_3909_, 1);
lean_inc_ref(v_binderType_3913_);
v_body_3914_ = lean_ctor_get(v_snd_3909_, 2);
lean_inc(v_toPure_3902_);
lean_inc(v___x_3901_);
lean_inc_ref(v_a_3906_);
lean_inc_ref(v_body_3914_);
v___f_3915_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3915_, 0, v_body_3914_);
lean_closure_set(v___f_3915_, 1, v_a_3906_);
lean_closure_set(v___f_3915_, 2, v___x_3901_);
lean_closure_set(v___f_3915_, 3, v_toPure_3902_);
if (lean_obj_tag(v_levels_x3f_3903_) == 0)
{
lean_object* v___f_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec(v___x_3901_);
v___f_3916_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3916_, 0, v_snd_3909_);
lean_closure_set(v___f_3916_, 1, v_toPure_3902_);
lean_closure_set(v___f_3916_, 2, v___f_3915_);
lean_inc(v_toBind_3905_);
lean_inc(v_inst_3904_);
v___f_3917_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3917_, 0, v_binderType_3913_);
lean_closure_set(v___f_3917_, 1, v_inst_3904_);
lean_closure_set(v___f_3917_, 2, v_toBind_3905_);
lean_closure_set(v___f_3917_, 3, v___f_3916_);
v___x_3918_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3918_, 0, v_a_3906_);
v___x_3919_ = lean_apply_2(v_inst_3904_, lean_box(0), v___x_3918_);
v___x_3920_ = lean_apply_4(v_toBind_3905_, lean_box(0), lean_box(0), v___x_3919_, v___f_3917_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_inc_ref(v_body_3914_);
lean_dec_ref(v___f_3915_);
lean_dec_ref(v_binderType_3913_);
lean_dec_ref_known(v_snd_3909_, 3);
lean_dec(v_toBind_3905_);
lean_dec(v_inst_3904_);
v___x_3921_ = lean_box(0);
v___x_3922_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3914_, v_a_3906_, v___x_3901_, v_toPure_3902_, v___x_3921_);
lean_dec_ref(v_a_3906_);
lean_dec_ref(v_body_3914_);
return v___x_3922_;
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_dec_ref(v_a_3906_);
lean_dec(v_toBind_3905_);
lean_dec(v_inst_3904_);
lean_dec(v___x_3901_);
v___x_3923_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3912_ == 0)
{
lean_ctor_set(v___x_3911_, 0, v___x_3923_);
v___x_3925_ = v___x_3911_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_snd_3909_);
v___x_3925_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___x_3927_ = lean_apply_2(v_toPure_3902_, lean_box(0), v___x_3926_);
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3931_, lean_object* v_toPure_3932_, lean_object* v_levels_x3f_3933_, lean_object* v_inst_3934_, lean_object* v_toBind_3935_, lean_object* v_a_3936_, lean_object* v_x_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3931_, v_toPure_3932_, v_levels_x3f_3933_, v_inst_3934_, v_toBind_3935_, v_a_3936_, v_x_3937_, v___y_3938_);
lean_dec(v_levels_x3f_3933_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3940_, lean_object* v_levels_x3f_3941_, lean_object* v_inst_3942_, lean_object* v_toBind_3943_, lean_object* v_params_3944_, lean_object* v_inst_3945_, lean_object* v___f_3946_, lean_object* v_val_3947_){
_start:
{
lean_object* v___x_3948_; lean_object* v___f_3949_; lean_object* v___x_3950_; size_t v_sz_3951_; size_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3948_ = lean_box(0);
lean_inc(v_toBind_3943_);
v___f_3949_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3949_, 0, v___x_3948_);
lean_closure_set(v___f_3949_, 1, v_toPure_3940_);
lean_closure_set(v___f_3949_, 2, v_levels_x3f_3941_);
lean_closure_set(v___f_3949_, 3, v_inst_3942_);
lean_closure_set(v___f_3949_, 4, v_toBind_3943_);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v_val_3947_);
v_sz_3951_ = lean_array_size(v_params_3944_);
v___x_3952_ = ((size_t)0ULL);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3945_, v_params_3944_, v___f_3949_, v_sz_3951_, v___x_3952_, v___x_3950_);
v___x_3954_ = lean_apply_4(v_toBind_3943_, lean_box(0), lean_box(0), v___x_3953_, v___f_3946_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3955_, lean_object* v_us_3956_, uint8_t v___x_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3955_, v_us_3956_, v___x_3957_, v___y_3960_, v___y_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3964_, lean_object* v_us_3965_, lean_object* v___x_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
uint8_t v___x_671__boxed_3972_; lean_object* v_res_3973_; 
v___x_671__boxed_3972_ = lean_unbox(v___x_3966_);
v_res_3973_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3964_, v_us_3965_, v___x_671__boxed_3972_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec_ref(v_cinfo_3964_);
return v_res_3973_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3977_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_3978_ = lean_unsigned_to_nat(2u);
v___x_3979_ = lean_unsigned_to_nat(202u);
v___x_3980_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_3981_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_3982_ = l_mkPanicMessageWithDecl(v___x_3981_, v___x_3980_, v___x_3979_, v___x_3978_, v___x_3977_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_3983_, lean_object* v___x_3984_, lean_object* v_inst_3985_, lean_object* v_toBind_3986_, lean_object* v___f_3987_, lean_object* v_us_3988_){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3989_ = l_List_lengthTR___redArg(v_us_3988_);
v___x_3990_ = l_Lean_ConstantInfo_levelParams(v_cinfo_3983_);
v___x_3991_ = l_List_lengthTR___redArg(v___x_3990_);
lean_dec(v___x_3990_);
v___x_3992_ = lean_nat_dec_eq(v___x_3989_, v___x_3991_);
lean_dec(v___x_3991_);
lean_dec(v___x_3989_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v_us_3988_);
lean_dec(v___f_3987_);
lean_dec(v_toBind_3986_);
lean_dec(v_inst_3985_);
lean_dec_ref(v_cinfo_3983_);
v___x_3993_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_3994_ = l_panic___redArg(v___x_3984_, v___x_3993_);
return v___x_3994_;
}
else
{
uint8_t v___x_3995_; lean_object* v___x_3996_; lean_object* v___f_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3995_ = 0;
v___x_3996_ = lean_box(v___x_3995_);
v___f_3997_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_3997_, 0, v_cinfo_3983_);
lean_closure_set(v___f_3997_, 1, v_us_3988_);
lean_closure_set(v___f_3997_, 2, v___x_3996_);
v___x_3998_ = lean_apply_2(v_inst_3985_, lean_box(0), v___f_3997_);
v___x_3999_ = lean_apply_4(v_toBind_3986_, lean_box(0), lean_box(0), v___x_3998_, v___f_3987_);
return v___x_3999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4000_, lean_object* v___x_4001_, lean_object* v_inst_4002_, lean_object* v_toBind_4003_, lean_object* v___f_4004_, lean_object* v_us_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4000_, v___x_4001_, v_inst_4002_, v_toBind_4003_, v___f_4004_, v_us_4005_);
lean_dec(v___x_4001_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4007_, lean_object* v_inst_4008_, lean_object* v_toBind_4009_, lean_object* v___f_4010_, lean_object* v_levels_x3f_4011_, lean_object* v_toPure_4012_, lean_object* v_cinfo_4013_){
_start:
{
lean_object* v___f_4014_; 
lean_inc(v_toBind_4009_);
lean_inc(v_inst_4008_);
lean_inc_ref(v_cinfo_4013_);
v___f_4014_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4014_, 0, v_cinfo_4013_);
lean_closure_set(v___f_4014_, 1, v___x_4007_);
lean_closure_set(v___f_4014_, 2, v_inst_4008_);
lean_closure_set(v___f_4014_, 3, v_toBind_4009_);
lean_closure_set(v___f_4014_, 4, v___f_4010_);
if (lean_obj_tag(v_levels_x3f_4011_) == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_dec(v_toPure_4012_);
v___x_4015_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4015_, 0, v_cinfo_4013_);
v___x_4016_ = lean_apply_2(v_inst_4008_, lean_box(0), v___x_4015_);
v___x_4017_ = lean_apply_4(v_toBind_4009_, lean_box(0), lean_box(0), v___x_4016_, v___f_4014_);
return v___x_4017_;
}
else
{
lean_object* v_val_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
lean_dec_ref(v_cinfo_4013_);
lean_dec(v_inst_4008_);
v_val_4018_ = lean_ctor_get(v_levels_x3f_4011_, 0);
lean_inc(v_val_4018_);
lean_dec_ref_known(v_levels_x3f_4011_, 1);
v___x_4019_ = lean_apply_2(v_toPure_4012_, lean_box(0), v_val_4018_);
v___x_4020_ = lean_apply_4(v_toBind_4009_, lean_box(0), lean_box(0), v___x_4019_, v___f_4014_);
return v___x_4020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4021_, lean_object* v_inst_4022_, lean_object* v_inst_4023_, lean_object* v_inst_4024_, lean_object* v_defaultFn_4025_, lean_object* v_levels_x3f_4026_, lean_object* v_params_4027_, lean_object* v_fieldVal_x3f_4028_){
_start:
{
lean_object* v_toApplicative_4029_; lean_object* v_toBind_4030_; lean_object* v_toPure_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___f_4034_; lean_object* v___f_4035_; lean_object* v___x_4036_; lean_object* v___f_4037_; lean_object* v___x_4038_; 
v_toApplicative_4029_ = lean_ctor_get(v_inst_4021_, 0);
v_toBind_4030_ = lean_ctor_get(v_inst_4021_, 1);
lean_inc_n(v_toBind_4030_, 3);
v_toPure_4031_ = lean_ctor_get(v_toApplicative_4029_, 1);
lean_inc_n(v_toPure_4031_, 3);
v___x_4032_ = lean_box(0);
lean_inc_ref_n(v_inst_4021_, 3);
v___x_4033_ = l_Lean_getConstInfo___redArg(v_inst_4021_, v_inst_4022_, v_inst_4023_, v_defaultFn_4025_);
lean_inc_n(v_inst_4024_, 2);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4034_, 0, v_inst_4021_);
lean_closure_set(v___f_4034_, 1, v_inst_4024_);
lean_closure_set(v___f_4034_, 2, v_fieldVal_x3f_4028_);
lean_closure_set(v___f_4034_, 3, v_toPure_4031_);
lean_inc(v_levels_x3f_4026_);
v___f_4035_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4035_, 0, v_toPure_4031_);
lean_closure_set(v___f_4035_, 1, v_levels_x3f_4026_);
lean_closure_set(v___f_4035_, 2, v_inst_4024_);
lean_closure_set(v___f_4035_, 3, v_toBind_4030_);
lean_closure_set(v___f_4035_, 4, v_params_4027_);
lean_closure_set(v___f_4035_, 5, v_inst_4021_);
lean_closure_set(v___f_4035_, 6, v___f_4034_);
v___x_4036_ = l_instInhabitedOfMonad___redArg(v_inst_4021_, v___x_4032_);
v___f_4037_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4037_, 0, v___x_4036_);
lean_closure_set(v___f_4037_, 1, v_inst_4024_);
lean_closure_set(v___f_4037_, 2, v_toBind_4030_);
lean_closure_set(v___f_4037_, 3, v___f_4035_);
lean_closure_set(v___f_4037_, 4, v_levels_x3f_4026_);
lean_closure_set(v___f_4037_, 5, v_toPure_4031_);
v___x_4038_ = lean_apply_4(v_toBind_4030_, lean_box(0), lean_box(0), v___x_4033_, v___f_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4039_, lean_object* v_inst_4040_, lean_object* v_inst_4041_, lean_object* v_inst_4042_, lean_object* v_inst_4043_, lean_object* v_inst_4044_, lean_object* v_defaultFn_4045_, lean_object* v_levels_x3f_4046_, lean_object* v_params_4047_, lean_object* v_fieldVal_x3f_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4040_, v_inst_4041_, v_inst_4042_, v_inst_4043_, v_defaultFn_4045_, v_levels_x3f_4046_, v_params_4047_, v_fieldVal_x3f_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_inst_4054_, lean_object* v_inst_4055_, lean_object* v_defaultFn_4056_, lean_object* v_levels_x3f_4057_, lean_object* v_params_4058_, lean_object* v_fieldVal_x3f_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4050_, v_inst_4051_, v_inst_4052_, v_inst_4053_, v_inst_4054_, v_inst_4055_, v_defaultFn_4056_, v_levels_x3f_4057_, v_params_4058_, v_fieldVal_x3f_4059_);
lean_dec_ref(v_inst_4055_);
return v_res_4060_;
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
