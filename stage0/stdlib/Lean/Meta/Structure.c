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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_498_ = lean_st_ref_set(v___y_478_, v___x_497_);
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
v___x_510_ = lean_st_ref_set(v___y_477_, v___x_509_);
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
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
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
v___x_593_ = lean_st_ref_set(v___y_574_, v___x_592_);
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
v___x_605_ = lean_st_ref_set(v___y_575_, v___x_604_);
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
lean_ctor_set(v___x_639_, 0, v___y_636_);
lean_ctor_set(v___x_639_, 1, v___y_632_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*3, v___x_559_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = l_Lean_addDecl(v___x_640_, v___y_631_, v___y_633_, v___y_634_);
lean_dec_ref(v___y_633_);
v___y_619_ = v___y_634_;
v___y_620_ = v___y_635_;
v___y_621_ = v___x_641_;
goto v___jp_618_;
}
v___jp_642_:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v_fileName_651_; lean_object* v_fileMap_652_; lean_object* v_options_653_; lean_object* v_currRecDepth_654_; lean_object* v_maxRecDepth_655_; lean_object* v_ref_656_; lean_object* v_currNamespace_657_; lean_object* v_openDecls_658_; lean_object* v_initHeartbeats_659_; lean_object* v_maxHeartbeats_660_; lean_object* v_quotContext_661_; lean_object* v_currMacroScope_662_; uint8_t v_diag_663_; lean_object* v_cancelTk_x3f_664_; uint8_t v_suppressElabErrors_665_; lean_object* v_inheritedTraceOptions_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_ref_671_; lean_object* v___x_672_; 
v___x_649_ = 0;
lean_inc_ref(v_a_560_);
v___x_650_ = l_Lean_LocalContext_mkForall(v_a_560_, v___x_561_, v___y_644_, v___x_559_, v___x_649_);
lean_dec_ref(v___y_644_);
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
if (v___y_643_ == 0)
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
v___y_631_ = v___x_649_;
v___y_632_ = v___x_670_;
v___y_633_ = v___x_672_;
v___y_634_ = v___y_648_;
v___y_635_ = v___y_646_;
v___y_636_ = v___x_689_;
goto v___jp_630_;
}
}
else
{
lean_dec_ref(v_env_688_);
v___y_631_ = v___x_649_;
v___y_632_ = v___x_670_;
v___y_633_ = v___x_672_;
v___y_634_ = v___y_648_;
v___y_635_ = v___y_646_;
v___y_636_ = v___x_689_;
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
v___y_643_ = v___x_702_;
v___y_644_ = v___x_699_;
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
v___y_643_ = v___x_718_;
v___y_644_ = v___x_699_;
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
v___y_643_ = v___x_727_;
v___y_644_ = v___x_699_;
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
v___x_806_ = lean_st_ref_set(v___y_784_, v___x_805_);
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
v___x_817_ = lean_st_ref_set(v___y_787_, v___x_816_);
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
v___x_862_ = lean_st_ref_set(v___y_840_, v___x_861_);
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
v___x_874_ = lean_st_ref_set(v___y_838_, v___x_873_);
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
v___x_1160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1158_, v___y_1157_, v___y_1153_, v___y_1156_, v___x_1159_, v___y_1151_, v___y_1152_, v___y_1155_, v___y_1154_);
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
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___x_1166_;
v___y_1154_ = v___y_1148_;
v___y_1155_ = v___y_1147_;
v___y_1156_ = v___f_1163_;
v___y_1157_ = v___x_1167_;
goto v___jp_1150_;
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = 3;
v___y_1151_ = v___y_1145_;
v___y_1152_ = v___y_1146_;
v___y_1153_ = v___x_1166_;
v___y_1154_ = v___y_1148_;
v___y_1155_ = v___y_1147_;
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
v___x_2313_ = lean_st_ref_set(v___y_2294_, v___x_2312_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2414_, lean_object* v_b_2415_, lean_object* v_x_2416_){
_start:
{
if (lean_obj_tag(v_x_2416_) == 0)
{
lean_dec(v_b_2415_);
lean_dec_ref(v_a_2414_);
return v_x_2416_;
}
else
{
lean_object* v_key_2417_; lean_object* v_value_2418_; lean_object* v_tail_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2431_; 
v_key_2417_ = lean_ctor_get(v_x_2416_, 0);
v_value_2418_ = lean_ctor_get(v_x_2416_, 1);
v_tail_2419_ = lean_ctor_get(v_x_2416_, 2);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2416_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2421_ = v_x_2416_;
v_isShared_2422_ = v_isSharedCheck_2431_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_tail_2419_);
lean_inc(v_value_2418_);
lean_inc(v_key_2417_);
lean_dec(v_x_2416_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2431_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Lean_ExprStructEq_beq(v_key_2417_, v_a_2414_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2414_, v_b_2415_, v_tail_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 2, v___x_2424_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_key_2417_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_value_2418_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
else
{
lean_object* v___x_2429_; 
lean_dec(v_value_2418_);
lean_dec(v_key_2417_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v_b_2415_);
lean_ctor_set(v___x_2421_, 0, v_a_2414_);
v___x_2429_ = v___x_2421_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2414_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_b_2415_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_tail_2419_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 0)
{
return v_x_2432_;
}
else
{
lean_object* v_key_2434_; lean_object* v_value_2435_; lean_object* v_tail_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2459_; 
v_key_2434_ = lean_ctor_get(v_x_2433_, 0);
v_value_2435_ = lean_ctor_get(v_x_2433_, 1);
v_tail_2436_ = lean_ctor_get(v_x_2433_, 2);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_x_2433_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2438_ = v_x_2433_;
v_isShared_2439_ = v_isSharedCheck_2459_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_tail_2436_);
lean_inc(v_value_2435_);
lean_inc(v_key_2434_);
lean_dec(v_x_2433_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2459_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v_fold_2444_; uint64_t v___x_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2440_ = lean_array_get_size(v_x_2432_);
v___x_2441_ = l_Lean_ExprStructEq_hash(v_key_2434_);
v___x_2442_ = 32ULL;
v___x_2443_ = lean_uint64_shift_right(v___x_2441_, v___x_2442_);
v_fold_2444_ = lean_uint64_xor(v___x_2441_, v___x_2443_);
v___x_2445_ = 16ULL;
v___x_2446_ = lean_uint64_shift_right(v_fold_2444_, v___x_2445_);
v___x_2447_ = lean_uint64_xor(v_fold_2444_, v___x_2446_);
v___x_2448_ = lean_uint64_to_usize(v___x_2447_);
v___x_2449_ = lean_usize_of_nat(v___x_2440_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_sub(v___x_2449_, v___x_2450_);
v___x_2452_ = lean_usize_land(v___x_2448_, v___x_2451_);
v___x_2453_ = lean_array_uget_borrowed(v_x_2432_, v___x_2452_);
lean_inc(v___x_2453_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 2, v___x_2453_);
v___x_2455_ = v___x_2438_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_key_2434_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_value_2435_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_array_uset(v_x_2432_, v___x_2452_, v___x_2455_);
v_x_2432_ = v___x_2456_;
v_x_2433_ = v_tail_2436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2460_, lean_object* v_source_2461_, lean_object* v_target_2462_){
_start:
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_array_get_size(v_source_2461_);
v___x_2464_ = lean_nat_dec_lt(v_i_2460_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_source_2461_);
lean_dec(v_i_2460_);
return v_target_2462_;
}
else
{
lean_object* v_es_2465_; lean_object* v___x_2466_; lean_object* v_source_2467_; lean_object* v_target_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_es_2465_ = lean_array_fget(v_source_2461_, v_i_2460_);
v___x_2466_ = lean_box(0);
v_source_2467_ = lean_array_fset(v_source_2461_, v_i_2460_, v___x_2466_);
v_target_2468_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2462_, v_es_2465_);
v___x_2469_ = lean_unsigned_to_nat(1u);
v___x_2470_ = lean_nat_add(v_i_2460_, v___x_2469_);
lean_dec(v_i_2460_);
v_i_2460_ = v___x_2470_;
v_source_2461_ = v_source_2467_;
v_target_2462_ = v_target_2468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_nbuckets_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2473_ = lean_array_get_size(v_data_2472_);
v___x_2474_ = lean_unsigned_to_nat(2u);
v_nbuckets_2475_ = lean_nat_mul(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_mk_array(v_nbuckets_2475_, v___x_2477_);
v___x_2479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2476_, v_data_2472_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2480_, lean_object* v_x_2481_){
_start:
{
if (lean_obj_tag(v_x_2481_) == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = 0;
return v___x_2482_;
}
else
{
lean_object* v_key_2483_; lean_object* v_tail_2484_; uint8_t v___x_2485_; 
v_key_2483_ = lean_ctor_get(v_x_2481_, 0);
v_tail_2484_ = lean_ctor_get(v_x_2481_, 2);
v___x_2485_ = l_Lean_ExprStructEq_beq(v_key_2483_, v_a_2480_);
if (v___x_2485_ == 0)
{
v_x_2481_ = v_tail_2484_;
goto _start;
}
else
{
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2487_, lean_object* v_x_2488_){
_start:
{
uint8_t v_res_2489_; lean_object* v_r_2490_; 
v_res_2489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2487_, v_x_2488_);
lean_dec(v_x_2488_);
lean_dec_ref(v_a_2487_);
v_r_2490_ = lean_box(v_res_2489_);
return v_r_2490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_){
_start:
{
lean_object* v_size_2494_; lean_object* v_buckets_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2538_; 
v_size_2494_ = lean_ctor_get(v_m_2491_, 0);
v_buckets_2495_ = lean_ctor_get(v_m_2491_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_m_2491_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2497_ = v_m_2491_;
v_isShared_2498_ = v_isSharedCheck_2538_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_buckets_2495_);
lean_inc(v_size_2494_);
lean_dec(v_m_2491_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2538_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; uint64_t v___x_2500_; uint64_t v___x_2501_; uint64_t v___x_2502_; uint64_t v_fold_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; lean_object* v_bkt_2512_; uint8_t v___x_2513_; 
v___x_2499_ = lean_array_get_size(v_buckets_2495_);
v___x_2500_ = l_Lean_ExprStructEq_hash(v_a_2492_);
v___x_2501_ = 32ULL;
v___x_2502_ = lean_uint64_shift_right(v___x_2500_, v___x_2501_);
v_fold_2503_ = lean_uint64_xor(v___x_2500_, v___x_2502_);
v___x_2504_ = 16ULL;
v___x_2505_ = lean_uint64_shift_right(v_fold_2503_, v___x_2504_);
v___x_2506_ = lean_uint64_xor(v_fold_2503_, v___x_2505_);
v___x_2507_ = lean_uint64_to_usize(v___x_2506_);
v___x_2508_ = lean_usize_of_nat(v___x_2499_);
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_sub(v___x_2508_, v___x_2509_);
v___x_2511_ = lean_usize_land(v___x_2507_, v___x_2510_);
v_bkt_2512_ = lean_array_uget_borrowed(v_buckets_2495_, v___x_2511_);
v___x_2513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2492_, v_bkt_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v_size_x27_2515_; lean_object* v___x_2516_; lean_object* v_buckets_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2514_ = lean_unsigned_to_nat(1u);
v_size_x27_2515_ = lean_nat_add(v_size_2494_, v___x_2514_);
lean_dec(v_size_2494_);
lean_inc(v_bkt_2512_);
v___x_2516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2492_);
lean_ctor_set(v___x_2516_, 1, v_b_2493_);
lean_ctor_set(v___x_2516_, 2, v_bkt_2512_);
v_buckets_x27_2517_ = lean_array_uset(v_buckets_2495_, v___x_2511_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(4u);
v___x_2519_ = lean_nat_mul(v_size_x27_2515_, v___x_2518_);
v___x_2520_ = lean_unsigned_to_nat(3u);
v___x_2521_ = lean_nat_div(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_array_get_size(v_buckets_x27_2517_);
v___x_2523_ = lean_nat_dec_le(v___x_2521_, v___x_2522_);
lean_dec(v___x_2521_);
if (v___x_2523_ == 0)
{
lean_object* v_val_2524_; lean_object* v___x_2526_; 
v_val_2524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2517_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v_val_2524_);
lean_ctor_set(v___x_2497_, 0, v_size_x27_2515_);
v___x_2526_ = v___x_2497_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_size_x27_2515_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
else
{
lean_object* v___x_2529_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v_buckets_x27_2517_);
lean_ctor_set(v___x_2497_, 0, v_size_x27_2515_);
v___x_2529_ = v___x_2497_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_size_x27_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_buckets_x27_2517_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v___x_2531_; lean_object* v_buckets_x27_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_inc(v_bkt_2512_);
v___x_2531_ = lean_box(0);
v_buckets_x27_2532_ = lean_array_uset(v_buckets_2495_, v___x_2511_, v___x_2531_);
v___x_2533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2492_, v_b_2493_, v_bkt_2512_);
v___x_2534_ = lean_array_uset(v_buckets_x27_2532_, v___x_2511_, v___x_2533_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v___x_2534_);
v___x_2536_ = v___x_2497_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_size_2494_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2539_, lean_object* v_e_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2543_ = lean_st_ref_take(v_a_2539_);
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2543_, v_e_2540_, v_a_2541_);
v___x_2545_ = lean_st_ref_set(v_a_2539_, v___x_2544_);
v___x_2546_ = lean_box(0);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2547_, lean_object* v_e_2548_, lean_object* v_a_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2547_, v_e_2548_, v_a_2549_);
lean_dec(v_a_2547_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2552_, lean_object* v_x_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_apply_1(v_x_2553_, lean_box(0));
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2561_, lean_object* v_x_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2561_, v_x_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2569_, lean_object* v_x_2570_){
_start:
{
if (lean_obj_tag(v_x_2570_) == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_box(0);
return v___x_2571_;
}
else
{
lean_object* v_key_2572_; lean_object* v_value_2573_; lean_object* v_tail_2574_; uint8_t v___x_2575_; 
v_key_2572_ = lean_ctor_get(v_x_2570_, 0);
v_value_2573_ = lean_ctor_get(v_x_2570_, 1);
v_tail_2574_ = lean_ctor_get(v_x_2570_, 2);
v___x_2575_ = l_Lean_ExprStructEq_beq(v_key_2572_, v_a_2569_);
if (v___x_2575_ == 0)
{
v_x_2570_ = v_tail_2574_;
goto _start;
}
else
{
lean_object* v___x_2577_; 
lean_inc(v_value_2573_);
v___x_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_value_2573_);
return v___x_2577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2578_, lean_object* v_x_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2578_, v_x_2579_);
lean_dec(v_x_2579_);
lean_dec_ref(v_a_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_buckets_2583_; lean_object* v___x_2584_; uint64_t v___x_2585_; uint64_t v___x_2586_; uint64_t v___x_2587_; uint64_t v_fold_2588_; uint64_t v___x_2589_; uint64_t v___x_2590_; uint64_t v___x_2591_; size_t v___x_2592_; size_t v___x_2593_; size_t v___x_2594_; size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_buckets_2583_ = lean_ctor_get(v_m_2581_, 1);
v___x_2584_ = lean_array_get_size(v_buckets_2583_);
v___x_2585_ = l_Lean_ExprStructEq_hash(v_a_2582_);
v___x_2586_ = 32ULL;
v___x_2587_ = lean_uint64_shift_right(v___x_2585_, v___x_2586_);
v_fold_2588_ = lean_uint64_xor(v___x_2585_, v___x_2587_);
v___x_2589_ = 16ULL;
v___x_2590_ = lean_uint64_shift_right(v_fold_2588_, v___x_2589_);
v___x_2591_ = lean_uint64_xor(v_fold_2588_, v___x_2590_);
v___x_2592_ = lean_uint64_to_usize(v___x_2591_);
v___x_2593_ = lean_usize_of_nat(v___x_2584_);
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_sub(v___x_2593_, v___x_2594_);
v___x_2596_ = lean_usize_land(v___x_2592_, v___x_2595_);
v___x_2597_ = lean_array_uget_borrowed(v_buckets_2583_, v___x_2596_);
v___x_2598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2582_, v___x_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2599_, v_a_2600_);
lean_dec_ref(v_a_2600_);
lean_dec_ref(v_m_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2602_, lean_object* v___y_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2607_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2603_);
v___x_2610_ = lean_apply_7(v_k_2602_, v_b_2604_, v___y_2603_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, lean_box(0));
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2611_, lean_object* v___y_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2611_, v___y_2612_, v_b_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2612_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2620_, uint8_t v_bi_2621_, lean_object* v_type_2622_, lean_object* v_k_2623_, uint8_t v_kind_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___f_2631_; lean_object* v___x_2632_; 
lean_inc(v___y_2625_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2631_, 0, v_k_2623_);
lean_closure_set(v___f_2631_, 1, v___y_2625_);
v___x_2632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2620_, v_bi_2621_, v_type_2622_, v___f_2631_, v_kind_2624_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
if (lean_obj_tag(v___x_2632_) == 0)
{
return v___x_2632_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2641_, lean_object* v_bi_2642_, lean_object* v_type_2643_, lean_object* v_k_2644_, lean_object* v_kind_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_bi_boxed_2652_; uint8_t v_kind_boxed_2653_; lean_object* v_res_2654_; 
v_bi_boxed_2652_ = lean_unbox(v_bi_2642_);
v_kind_boxed_2653_ = lean_unbox(v_kind_2645_);
v_res_2654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2641_, v_bi_boxed_2652_, v_type_2643_, v_k_2644_, v_kind_boxed_2653_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2655_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2669_, lean_object* v_type_2670_, lean_object* v_val_2671_, lean_object* v_k_2672_, uint8_t v_nondep_2673_, uint8_t v_kind_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___f_2681_; lean_object* v___x_2682_; 
lean_inc(v___y_2675_);
v___f_2681_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2681_, 0, v_k_2672_);
lean_closure_set(v___f_2681_, 1, v___y_2675_);
v___x_2682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2669_, v_type_2670_, v_val_2671_, v___f_2681_, v_nondep_2673_, v_kind_2674_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2682_) == 0)
{
return v___x_2682_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2691_, lean_object* v_type_2692_, lean_object* v_val_2693_, lean_object* v_k_2694_, lean_object* v_nondep_2695_, lean_object* v_kind_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v_nondep_boxed_2703_; uint8_t v_kind_boxed_2704_; lean_object* v_res_2705_; 
v_nondep_boxed_2703_ = lean_unbox(v_nondep_2695_);
v_kind_boxed_2704_ = lean_unbox(v_kind_2696_);
v_res_2705_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2691_, v_type_2692_, v_val_2693_, v_k_2694_, v_nondep_boxed_2703_, v_kind_boxed_2704_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
return v_res_2705_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = l_Lean_maxRecDepthErrorMessage;
v___x_2712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2714_ = l_Lean_MessageData_ofFormat(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2716_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2717_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2718_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_ref_2718_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___y_2734_; lean_object* v_fileName_2743_; lean_object* v_fileMap_2744_; lean_object* v_options_2745_; lean_object* v_currRecDepth_2746_; lean_object* v_maxRecDepth_2747_; lean_object* v_ref_2748_; lean_object* v_currNamespace_2749_; lean_object* v_openDecls_2750_; lean_object* v_initHeartbeats_2751_; lean_object* v_maxHeartbeats_2752_; lean_object* v_quotContext_2753_; lean_object* v_currMacroScope_2754_; uint8_t v_diag_2755_; lean_object* v_cancelTk_x3f_2756_; uint8_t v_suppressElabErrors_2757_; lean_object* v_inheritedTraceOptions_2758_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_fileName_2743_ = lean_ctor_get(v___y_2730_, 0);
v_fileMap_2744_ = lean_ctor_get(v___y_2730_, 1);
v_options_2745_ = lean_ctor_get(v___y_2730_, 2);
v_currRecDepth_2746_ = lean_ctor_get(v___y_2730_, 3);
v_maxRecDepth_2747_ = lean_ctor_get(v___y_2730_, 4);
v_ref_2748_ = lean_ctor_get(v___y_2730_, 5);
v_currNamespace_2749_ = lean_ctor_get(v___y_2730_, 6);
v_openDecls_2750_ = lean_ctor_get(v___y_2730_, 7);
v_initHeartbeats_2751_ = lean_ctor_get(v___y_2730_, 8);
v_maxHeartbeats_2752_ = lean_ctor_get(v___y_2730_, 9);
v_quotContext_2753_ = lean_ctor_get(v___y_2730_, 10);
v_currMacroScope_2754_ = lean_ctor_get(v___y_2730_, 11);
v_diag_2755_ = lean_ctor_get_uint8(v___y_2730_, sizeof(void*)*14);
v_cancelTk_x3f_2756_ = lean_ctor_get(v___y_2730_, 12);
v_suppressElabErrors_2757_ = lean_ctor_get_uint8(v___y_2730_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2758_ = lean_ctor_get(v___y_2730_, 13);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_nat_dec_eq(v_maxRecDepth_2747_, v___x_2764_);
if (v___x_2765_ == 0)
{
uint8_t v___x_2766_; 
v___x_2766_ = lean_nat_dec_eq(v_currRecDepth_2746_, v_maxRecDepth_2747_);
if (v___x_2766_ == 0)
{
goto v___jp_2759_;
}
else
{
lean_object* v___x_2767_; 
lean_dec_ref(v_x_2726_);
lean_inc(v_ref_2748_);
v___x_2767_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2748_);
v___y_2734_ = v___x_2767_;
goto v___jp_2733_;
}
}
else
{
goto v___jp_2759_;
}
v___jp_2733_:
{
if (lean_obj_tag(v___y_2734_) == 0)
{
return v___y_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_a_2735_ = lean_ctor_get(v___y_2734_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___y_2734_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___y_2734_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___y_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
v___jp_2759_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = lean_unsigned_to_nat(1u);
v___x_2761_ = lean_nat_add(v_currRecDepth_2746_, v___x_2760_);
lean_inc_ref(v_inheritedTraceOptions_2758_);
lean_inc(v_cancelTk_x3f_2756_);
lean_inc(v_currMacroScope_2754_);
lean_inc(v_quotContext_2753_);
lean_inc(v_maxHeartbeats_2752_);
lean_inc(v_initHeartbeats_2751_);
lean_inc(v_openDecls_2750_);
lean_inc(v_currNamespace_2749_);
lean_inc(v_ref_2748_);
lean_inc(v_maxRecDepth_2747_);
lean_inc_ref(v_options_2745_);
lean_inc_ref(v_fileMap_2744_);
lean_inc_ref(v_fileName_2743_);
v___x_2762_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2762_, 0, v_fileName_2743_);
lean_ctor_set(v___x_2762_, 1, v_fileMap_2744_);
lean_ctor_set(v___x_2762_, 2, v_options_2745_);
lean_ctor_set(v___x_2762_, 3, v___x_2761_);
lean_ctor_set(v___x_2762_, 4, v_maxRecDepth_2747_);
lean_ctor_set(v___x_2762_, 5, v_ref_2748_);
lean_ctor_set(v___x_2762_, 6, v_currNamespace_2749_);
lean_ctor_set(v___x_2762_, 7, v_openDecls_2750_);
lean_ctor_set(v___x_2762_, 8, v_initHeartbeats_2751_);
lean_ctor_set(v___x_2762_, 9, v_maxHeartbeats_2752_);
lean_ctor_set(v___x_2762_, 10, v_quotContext_2753_);
lean_ctor_set(v___x_2762_, 11, v_currMacroScope_2754_);
lean_ctor_set(v___x_2762_, 12, v_cancelTk_x3f_2756_);
lean_ctor_set(v___x_2762_, 13, v_inheritedTraceOptions_2758_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*14, v_diag_2755_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*14 + 1, v_suppressElabErrors_2757_);
lean_inc(v___y_2731_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
v___x_2763_ = lean_apply_6(v_x_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___x_2762_, v___y_2731_, lean_box(0));
v___y_2734_ = v___x_2763_;
goto v___jp_2733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2779_, lean_object* v_pre_2780_, lean_object* v_post_2781_, uint8_t v_usedLetOnly_2782_, uint8_t v_skipConstInApp_2783_, uint8_t v_skipInstances_2784_, lean_object* v_body_2785_, lean_object* v_x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_array_push(v_fvars_2779_, v_x_2786_);
v___x_2794_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2780_, v_post_2781_, v_usedLetOnly_2782_, v_skipConstInApp_2783_, v_skipInstances_2784_, v___x_2793_, v_body_2785_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2795_, lean_object* v_pre_2796_, lean_object* v_post_2797_, lean_object* v_usedLetOnly_2798_, lean_object* v_skipConstInApp_2799_, lean_object* v_skipInstances_2800_, lean_object* v_body_2801_, lean_object* v_x_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v_usedLetOnly_boxed_2809_; uint8_t v_skipConstInApp_boxed_2810_; uint8_t v_skipInstances_boxed_2811_; lean_object* v_res_2812_; 
v_usedLetOnly_boxed_2809_ = lean_unbox(v_usedLetOnly_2798_);
v_skipConstInApp_boxed_2810_ = lean_unbox(v_skipConstInApp_2799_);
v_skipInstances_boxed_2811_ = lean_unbox(v_skipInstances_2800_);
v_res_2812_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2795_, v_pre_2796_, v_post_2797_, v_usedLetOnly_boxed_2809_, v_skipConstInApp_boxed_2810_, v_skipInstances_boxed_2811_, v_body_2801_, v_x_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2813_, lean_object* v_post_2814_, uint8_t v_usedLetOnly_2815_, uint8_t v_skipConstInApp_2816_, uint8_t v_skipInstances_2817_, lean_object* v_e_2818_, lean_object* v_a_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
lean_inc_ref(v_post_2814_);
lean_inc(v___y_2823_);
lean_inc_ref(v___y_2822_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc_ref(v_e_2818_);
v___x_2825_ = lean_apply_6(v_post_2814_, v_e_2818_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2844_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2844_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2844_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
switch(lean_obj_tag(v_a_2826_))
{
case 0:
{
lean_object* v_e_2830_; lean_object* v___x_2832_; 
lean_dec_ref(v_e_2818_);
lean_dec_ref(v_post_2814_);
lean_dec_ref(v_pre_2813_);
v_e_2830_ = lean_ctor_get(v_a_2826_, 0);
lean_inc_ref(v_e_2830_);
lean_dec_ref_known(v_a_2826_, 1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v_e_2830_);
v___x_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_e_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
case 1:
{
lean_object* v_e_2834_; lean_object* v___x_2835_; 
lean_del_object(v___x_2828_);
lean_dec_ref(v_e_2818_);
v_e_2834_ = lean_ctor_get(v_a_2826_, 0);
lean_inc_ref(v_e_2834_);
lean_dec_ref_known(v_a_2826_, 1);
v___x_2835_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2813_, v_post_2814_, v_usedLetOnly_2815_, v_skipConstInApp_2816_, v_skipInstances_2817_, v_e_2834_, v_a_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2835_;
}
default: 
{
lean_object* v_e_x3f_2836_; 
lean_dec_ref(v_post_2814_);
lean_dec_ref(v_pre_2813_);
v_e_x3f_2836_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_e_x3f_2836_);
lean_dec_ref_known(v_a_2826_, 1);
if (lean_obj_tag(v_e_x3f_2836_) == 0)
{
lean_object* v___x_2838_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v_e_2818_);
v___x_2838_ = v___x_2828_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_e_2818_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2842_; 
lean_dec_ref(v_e_2818_);
v_val_2840_ = lean_ctor_get(v_e_x3f_2836_, 0);
lean_inc(v_val_2840_);
lean_dec_ref_known(v_e_x3f_2836_, 1);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v_val_2840_);
v___x_2842_ = v___x_2828_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_val_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v_e_2818_);
lean_dec_ref(v_post_2814_);
lean_dec_ref(v_pre_2813_);
v_a_2845_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2825_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2825_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2853_, lean_object* v_post_2854_, uint8_t v_usedLetOnly_2855_, uint8_t v_skipConstInApp_2856_, uint8_t v_skipInstances_2857_, lean_object* v_fvars_2858_, lean_object* v_e_2859_, lean_object* v_a_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
if (lean_obj_tag(v_e_2859_) == 6)
{
lean_object* v_binderName_2866_; lean_object* v_binderType_2867_; lean_object* v_body_2868_; uint8_t v_binderInfo_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_binderName_2866_ = lean_ctor_get(v_e_2859_, 0);
lean_inc(v_binderName_2866_);
v_binderType_2867_ = lean_ctor_get(v_e_2859_, 1);
lean_inc_ref(v_binderType_2867_);
v_body_2868_ = lean_ctor_get(v_e_2859_, 2);
lean_inc_ref(v_body_2868_);
v_binderInfo_2869_ = lean_ctor_get_uint8(v_e_2859_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2859_, 3);
v___x_2870_ = lean_expr_instantiate_rev(v_binderType_2867_, v_fvars_2858_);
lean_dec_ref(v_binderType_2867_);
lean_inc_ref(v_post_2854_);
lean_inc_ref(v_pre_2853_);
v___x_2871_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2853_, v_post_2854_, v_usedLetOnly_2855_, v_skipConstInApp_2856_, v_skipInstances_2857_, v___x_2870_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; uint8_t v___x_2877_; lean_object* v___x_2878_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_box(v_usedLetOnly_2855_);
v___x_2874_ = lean_box(v_skipConstInApp_2856_);
v___x_2875_ = lean_box(v_skipInstances_2857_);
v___f_2876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2876_, 0, v_fvars_2858_);
lean_closure_set(v___f_2876_, 1, v_pre_2853_);
lean_closure_set(v___f_2876_, 2, v_post_2854_);
lean_closure_set(v___f_2876_, 3, v___x_2873_);
lean_closure_set(v___f_2876_, 4, v___x_2874_);
lean_closure_set(v___f_2876_, 5, v___x_2875_);
lean_closure_set(v___f_2876_, 6, v_body_2868_);
v___x_2877_ = 0;
v___x_2878_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2866_, v_binderInfo_2869_, v_a_2872_, v___f_2876_, v___x_2877_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2878_;
}
else
{
lean_dec_ref(v_body_2868_);
lean_dec(v_binderName_2866_);
lean_dec_ref(v_fvars_2858_);
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
return v___x_2871_;
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_expr_instantiate_rev(v_e_2859_, v_fvars_2858_);
lean_dec_ref(v_e_2859_);
lean_inc_ref(v_post_2854_);
lean_inc_ref(v_pre_2853_);
v___x_2880_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2853_, v_post_2854_, v_usedLetOnly_2855_, v_skipConstInApp_2856_, v_skipInstances_2857_, v___x_2879_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; uint8_t v___x_2882_; uint8_t v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = 0;
v___x_2883_ = 1;
v___x_2884_ = 1;
v___x_2885_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2858_, v_a_2881_, v___x_2882_, v_usedLetOnly_2855_, v___x_2882_, v___x_2883_, v___x_2884_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec_ref(v_fvars_2858_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2853_, v_post_2854_, v_usedLetOnly_2855_, v_skipConstInApp_2856_, v_skipInstances_2857_, v_a_2886_, v_a_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2887_;
}
else
{
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
return v___x_2885_;
}
}
else
{
lean_dec_ref(v_fvars_2858_);
lean_dec_ref(v_post_2854_);
lean_dec_ref(v_pre_2853_);
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2888_, lean_object* v_pre_2889_, lean_object* v_post_2890_, uint8_t v_usedLetOnly_2891_, uint8_t v_skipConstInApp_2892_, uint8_t v_skipInstances_2893_, lean_object* v_body_2894_, lean_object* v_x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_array_push(v_fvars_2888_, v_x_2895_);
v___x_2903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2889_, v_post_2890_, v_usedLetOnly_2891_, v_skipConstInApp_2892_, v_skipInstances_2893_, v___x_2902_, v_body_2894_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2904_, lean_object* v_pre_2905_, lean_object* v_post_2906_, lean_object* v_usedLetOnly_2907_, lean_object* v_skipConstInApp_2908_, lean_object* v_skipInstances_2909_, lean_object* v_body_2910_, lean_object* v_x_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v_usedLetOnly_boxed_2918_; uint8_t v_skipConstInApp_boxed_2919_; uint8_t v_skipInstances_boxed_2920_; lean_object* v_res_2921_; 
v_usedLetOnly_boxed_2918_ = lean_unbox(v_usedLetOnly_2907_);
v_skipConstInApp_boxed_2919_ = lean_unbox(v_skipConstInApp_2908_);
v_skipInstances_boxed_2920_ = lean_unbox(v_skipInstances_2909_);
v_res_2921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2904_, v_pre_2905_, v_post_2906_, v_usedLetOnly_boxed_2918_, v_skipConstInApp_boxed_2919_, v_skipInstances_boxed_2920_, v_body_2910_, v_x_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2922_, lean_object* v_post_2923_, uint8_t v_usedLetOnly_2924_, uint8_t v_skipConstInApp_2925_, uint8_t v_skipInstances_2926_, lean_object* v_fvars_2927_, lean_object* v_e_2928_, lean_object* v_a_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
if (lean_obj_tag(v_e_2928_) == 8)
{
lean_object* v_declName_2935_; lean_object* v_type_2936_; lean_object* v_value_2937_; lean_object* v_body_2938_; uint8_t v_nondep_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_declName_2935_ = lean_ctor_get(v_e_2928_, 0);
lean_inc(v_declName_2935_);
v_type_2936_ = lean_ctor_get(v_e_2928_, 1);
lean_inc_ref(v_type_2936_);
v_value_2937_ = lean_ctor_get(v_e_2928_, 2);
lean_inc_ref(v_value_2937_);
v_body_2938_ = lean_ctor_get(v_e_2928_, 3);
lean_inc_ref(v_body_2938_);
v_nondep_2939_ = lean_ctor_get_uint8(v_e_2928_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2928_, 4);
v___x_2940_ = lean_expr_instantiate_rev(v_type_2936_, v_fvars_2927_);
lean_dec_ref(v_type_2936_);
lean_inc_ref(v_post_2923_);
lean_inc_ref(v_pre_2922_);
v___x_2941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2922_, v_post_2923_, v_usedLetOnly_2924_, v_skipConstInApp_2925_, v_skipInstances_2926_, v___x_2940_, v_a_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = lean_expr_instantiate_rev(v_value_2937_, v_fvars_2927_);
lean_dec_ref(v_value_2937_);
lean_inc_ref(v_post_2923_);
lean_inc_ref(v_pre_2922_);
v___x_2944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2922_, v_post_2923_, v_usedLetOnly_2924_, v_skipConstInApp_2925_, v_skipInstances_2926_, v___x_2943_, v_a_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___f_2949_; uint8_t v___x_2950_; lean_object* v___x_2951_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v___x_2946_ = lean_box(v_usedLetOnly_2924_);
v___x_2947_ = lean_box(v_skipConstInApp_2925_);
v___x_2948_ = lean_box(v_skipInstances_2926_);
v___f_2949_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2949_, 0, v_fvars_2927_);
lean_closure_set(v___f_2949_, 1, v_pre_2922_);
lean_closure_set(v___f_2949_, 2, v_post_2923_);
lean_closure_set(v___f_2949_, 3, v___x_2946_);
lean_closure_set(v___f_2949_, 4, v___x_2947_);
lean_closure_set(v___f_2949_, 5, v___x_2948_);
lean_closure_set(v___f_2949_, 6, v_body_2938_);
v___x_2950_ = 0;
v___x_2951_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2935_, v_a_2942_, v_a_2945_, v___f_2949_, v_nondep_2939_, v___x_2950_, v_a_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2951_;
}
else
{
lean_dec(v_a_2942_);
lean_dec_ref(v_body_2938_);
lean_dec(v_declName_2935_);
lean_dec_ref(v_fvars_2927_);
lean_dec_ref(v_post_2923_);
lean_dec_ref(v_pre_2922_);
return v___x_2944_;
}
}
else
{
lean_dec_ref(v_body_2938_);
lean_dec_ref(v_value_2937_);
lean_dec(v_declName_2935_);
lean_dec_ref(v_fvars_2927_);
lean_dec_ref(v_post_2923_);
lean_dec_ref(v_pre_2922_);
return v___x_2941_;
}
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_expr_instantiate_rev(v_e_2928_, v_fvars_2927_);
lean_dec_ref(v_e_2928_);
lean_inc_ref(v_post_2923_);
lean_inc_ref(v_pre_2922_);
v___x_2953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2922_, v_post_2923_, v_usedLetOnly_2924_, v_skipConstInApp_2925_, v_skipInstances_2926_, v___x_2952_, v_a_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; uint8_t v___x_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = 0;
v___x_2956_ = 1;
v___x_2957_ = l_Lean_Meta_mkLetFVars(v_fvars_2927_, v_a_2954_, v_usedLetOnly_2924_, v___x_2955_, v___x_2956_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec_ref(v_fvars_2927_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2922_, v_post_2923_, v_usedLetOnly_2924_, v_skipConstInApp_2925_, v_skipInstances_2926_, v_a_2958_, v_a_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2959_;
}
else
{
lean_dec_ref(v_post_2923_);
lean_dec_ref(v_pre_2922_);
return v___x_2957_;
}
}
else
{
lean_dec_ref(v_fvars_2927_);
lean_dec_ref(v_post_2923_);
lean_dec_ref(v_pre_2922_);
return v___x_2953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2960_, lean_object* v_post_2961_, uint8_t v_usedLetOnly_2962_, uint8_t v_skipConstInApp_2963_, uint8_t v_skipInstances_2964_, size_t v_sz_2965_, size_t v_i_2966_, lean_object* v_bs_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v___x_2974_; 
v___x_2974_ = lean_usize_dec_lt(v_i_2966_, v_sz_2965_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec_ref(v_post_2961_);
lean_dec_ref(v_pre_2960_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_bs_2967_);
return v___x_2975_;
}
else
{
lean_object* v_v_2976_; lean_object* v___x_2977_; 
v_v_2976_ = lean_array_uget_borrowed(v_bs_2967_, v_i_2966_);
lean_inc(v_v_2976_);
lean_inc_ref(v_post_2961_);
lean_inc_ref(v_pre_2960_);
v___x_2977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2960_, v_post_2961_, v_usedLetOnly_2962_, v_skipConstInApp_2963_, v_skipInstances_2964_, v_v_2976_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v_bs_x27_2980_; size_t v___x_2981_; size_t v___x_2982_; lean_object* v___x_2983_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = lean_unsigned_to_nat(0u);
v_bs_x27_2980_ = lean_array_uset(v_bs_2967_, v_i_2966_, v___x_2979_);
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = lean_usize_add(v_i_2966_, v___x_2981_);
v___x_2983_ = lean_array_uset(v_bs_x27_2980_, v_i_2966_, v_a_2978_);
v_i_2966_ = v___x_2982_;
v_bs_2967_ = v___x_2983_;
goto _start;
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v_bs_2967_);
lean_dec_ref(v_post_2961_);
lean_dec_ref(v_pre_2960_);
v_a_2985_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2977_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2977_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2993_, lean_object* v_post_2994_, uint8_t v_usedLetOnly_2995_, uint8_t v_skipConstInApp_2996_, uint8_t v_skipInstances_2997_, lean_object* v___x_2998_, lean_object* v___y_2999_, lean_object* v_b_3000_, lean_object* v_a_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2993_, v_post_2994_, v_usedLetOnly_2995_, v_skipConstInApp_2996_, v_skipInstances_2997_, v___x_2998_, v___y_2999_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3017_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3017_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3017_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3012_ = lean_array_fset(v_b_3000_, v_a_3001_, v_a_3008_);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3013_);
v___x_3015_ = v___x_3010_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v_b_3000_);
v_a_3018_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3007_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3007_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3026_, lean_object* v_post_3027_, lean_object* v_usedLetOnly_3028_, lean_object* v_skipConstInApp_3029_, lean_object* v_skipInstances_3030_, lean_object* v___x_3031_, lean_object* v___y_3032_, lean_object* v_b_3033_, lean_object* v_a_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v_usedLetOnly_boxed_3040_; uint8_t v_skipConstInApp_boxed_3041_; uint8_t v_skipInstances_boxed_3042_; lean_object* v_res_3043_; 
v_usedLetOnly_boxed_3040_ = lean_unbox(v_usedLetOnly_3028_);
v_skipConstInApp_boxed_3041_ = lean_unbox(v_skipConstInApp_3029_);
v_skipInstances_boxed_3042_ = lean_unbox(v_skipInstances_3030_);
v_res_3043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3026_, v_post_3027_, v_usedLetOnly_boxed_3040_, v_skipConstInApp_boxed_3041_, v_skipInstances_boxed_3042_, v___x_3031_, v___y_3032_, v_b_3033_, v_a_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v_a_3034_);
lean_dec(v___y_3032_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3044_, lean_object* v___x_3045_, lean_object* v_pre_3046_, lean_object* v_post_3047_, uint8_t v_usedLetOnly_3048_, uint8_t v_skipConstInApp_3049_, uint8_t v_skipInstances_3050_, lean_object* v_a_3051_, lean_object* v_b_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v___y_3060_; uint8_t v___x_3083_; 
v___x_3083_ = lean_nat_dec_lt(v_a_3051_, v_upperBound_3044_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
lean_dec(v_a_3051_);
lean_dec_ref(v_post_3047_);
lean_dec_ref(v_pre_3046_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v_b_3052_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v___x_3085_ = lean_array_fget_borrowed(v_b_3052_, v_a_3051_);
v___x_3086_ = lean_array_get_size(v___x_3045_);
v___x_3087_ = lean_nat_dec_lt(v_a_3051_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___f_3091_; 
lean_inc(v___x_3085_);
v___x_3088_ = lean_box(v_usedLetOnly_3048_);
v___x_3089_ = lean_box(v_skipConstInApp_3049_);
v___x_3090_ = lean_box(v_skipInstances_3050_);
lean_inc(v_a_3051_);
lean_inc(v___y_3053_);
lean_inc_ref(v_post_3047_);
lean_inc_ref(v_pre_3046_);
v___f_3091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3091_, 0, v_pre_3046_);
lean_closure_set(v___f_3091_, 1, v_post_3047_);
lean_closure_set(v___f_3091_, 2, v___x_3088_);
lean_closure_set(v___f_3091_, 3, v___x_3089_);
lean_closure_set(v___f_3091_, 4, v___x_3090_);
lean_closure_set(v___f_3091_, 5, v___x_3085_);
lean_closure_set(v___f_3091_, 6, v___y_3053_);
lean_closure_set(v___f_3091_, 7, v_b_3052_);
lean_closure_set(v___f_3091_, 8, v_a_3051_);
v___y_3060_ = v___f_3091_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3092_; uint8_t v_isInstance_3093_; 
v___x_3092_ = lean_array_fget_borrowed(v___x_3045_, v_a_3051_);
v_isInstance_3093_ = lean_ctor_get_uint8(v___x_3092_, sizeof(void*)*1 + 4);
if (v_isInstance_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; 
lean_inc(v___x_3085_);
v___x_3094_ = lean_box(v_usedLetOnly_3048_);
v___x_3095_ = lean_box(v_skipConstInApp_3049_);
v___x_3096_ = lean_box(v_skipInstances_3050_);
lean_inc(v_a_3051_);
lean_inc(v___y_3053_);
lean_inc_ref(v_post_3047_);
lean_inc_ref(v_pre_3046_);
v___f_3097_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3097_, 0, v_pre_3046_);
lean_closure_set(v___f_3097_, 1, v_post_3047_);
lean_closure_set(v___f_3097_, 2, v___x_3094_);
lean_closure_set(v___f_3097_, 3, v___x_3095_);
lean_closure_set(v___f_3097_, 4, v___x_3096_);
lean_closure_set(v___f_3097_, 5, v___x_3085_);
lean_closure_set(v___f_3097_, 6, v___y_3053_);
lean_closure_set(v___f_3097_, 7, v_b_3052_);
lean_closure_set(v___f_3097_, 8, v_a_3051_);
v___y_3060_ = v___f_3097_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3098_; lean_object* v___f_3099_; 
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_b_3052_);
v___f_3099_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3099_, 0, v___x_3098_);
v___y_3060_ = v___f_3099_;
goto v___jp_3059_;
}
}
}
v___jp_3059_:
{
lean_object* v___x_3061_; 
lean_inc(v___y_3057_);
lean_inc_ref(v___y_3056_);
lean_inc(v___y_3055_);
lean_inc_ref(v___y_3054_);
v___x_3061_ = lean_apply_5(v___y_3060_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, lean_box(0));
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3074_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3074_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
if (lean_obj_tag(v_a_3062_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; 
lean_dec(v_a_3051_);
lean_dec_ref(v_post_3047_);
lean_dec_ref(v_pre_3046_);
v_a_3066_ = lean_ctor_get(v_a_3062_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v_a_3062_, 1);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v_a_3066_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3066_);
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
lean_object* v_a_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3064_);
v_a_3070_ = lean_ctor_get(v_a_3062_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v_a_3062_, 1);
v___x_3071_ = lean_unsigned_to_nat(1u);
v___x_3072_ = lean_nat_add(v_a_3051_, v___x_3071_);
lean_dec(v_a_3051_);
v_a_3051_ = v___x_3072_;
v_b_3052_ = v_a_3070_;
goto _start;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_3051_);
lean_dec_ref(v_post_3047_);
lean_dec_ref(v_pre_3046_);
v_a_3075_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3061_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3061_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3100_, lean_object* v_pre_3101_, lean_object* v_post_3102_, uint8_t v_usedLetOnly_3103_, uint8_t v_skipConstInApp_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_f_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; 
if (lean_obj_tag(v_x_3105_) == 5)
{
lean_object* v_fn_3163_; lean_object* v_arg_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_fn_3163_ = lean_ctor_get(v_x_3105_, 0);
lean_inc_ref(v_fn_3163_);
v_arg_3164_ = lean_ctor_get(v_x_3105_, 1);
lean_inc_ref(v_arg_3164_);
lean_dec_ref_known(v_x_3105_, 2);
v___x_3165_ = lean_array_set(v_x_3106_, v_x_3107_, v_arg_3164_);
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_sub(v_x_3107_, v___x_3166_);
lean_dec(v_x_3107_);
v_x_3105_ = v_fn_3163_;
v_x_3106_ = v___x_3165_;
v_x_3107_ = v___x_3167_;
goto _start;
}
else
{
lean_dec(v_x_3107_);
if (v_skipConstInApp_3104_ == 0)
{
goto v___jp_3160_;
}
else
{
uint8_t v___x_3169_; 
v___x_3169_ = l_Lean_Expr_isConst(v_x_3105_);
if (v___x_3169_ == 0)
{
goto v___jp_3160_;
}
else
{
v_f_3115_ = v_x_3105_;
v___y_3116_ = v___y_3108_;
v___y_3117_ = v___y_3109_;
v___y_3118_ = v___y_3110_;
v___y_3119_ = v___y_3111_;
v___y_3120_ = v___y_3112_;
goto v___jp_3114_;
}
}
}
v___jp_3114_:
{
if (v_skipInstances_3100_ == 0)
{
size_t v_sz_3121_; size_t v___x_3122_; lean_object* v___x_3123_; 
v_sz_3121_ = lean_array_size(v_x_3106_);
v___x_3122_ = ((size_t)0ULL);
lean_inc_ref(v_post_3102_);
lean_inc_ref(v_pre_3101_);
v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3100_, v_sz_3121_, v___x_3122_, v_x_3106_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___x_3125_ = l_Lean_mkAppN(v_f_3115_, v_a_3124_);
lean_dec(v_a_3124_);
v___x_3126_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3100_, v___x_3125_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
return v___x_3126_;
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_f_3115_);
lean_dec_ref(v_post_3102_);
lean_dec_ref(v_pre_3101_);
v_a_3127_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3123_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3123_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_x_3106_);
lean_inc_ref(v_f_3115_);
v___x_3136_ = l_Lean_Meta_getFunInfoNArgs(v_f_3115_, v___x_3135_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v_paramInfo_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v_paramInfo_3138_ = lean_ctor_get(v_a_3137_, 0);
lean_inc_ref(v_paramInfo_3138_);
lean_dec(v_a_3137_);
v___x_3139_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3102_);
lean_inc_ref(v_pre_3101_);
v___x_3140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3135_, v_paramInfo_3138_, v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3100_, v___x_3139_, v_x_3106_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec_ref(v_paramInfo_3138_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = l_Lean_mkAppN(v_f_3115_, v_a_3141_);
lean_dec(v_a_3141_);
v___x_3143_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3100_, v___x_3142_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
return v___x_3143_;
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v_f_3115_);
lean_dec_ref(v_post_3102_);
lean_dec_ref(v_pre_3101_);
v_a_3144_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3140_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3140_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_f_3115_);
lean_dec_ref(v_x_3106_);
lean_dec_ref(v_post_3102_);
lean_dec_ref(v_pre_3101_);
v_a_3152_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3136_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3136_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
v___jp_3160_:
{
lean_object* v___x_3161_; 
lean_inc_ref(v_post_3102_);
lean_inc_ref(v_pre_3101_);
v___x_3161_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3100_, v_x_3105_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v_f_3115_ = v_a_3162_;
v___y_3116_ = v___y_3108_;
v___y_3117_ = v___y_3109_;
v___y_3118_ = v___y_3110_;
v___y_3119_ = v___y_3111_;
v___y_3120_ = v___y_3112_;
goto v___jp_3114_;
}
else
{
lean_dec_ref(v_x_3106_);
lean_dec_ref(v_post_3102_);
lean_dec_ref(v_pre_3101_);
return v___x_3161_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3170_, lean_object* v_pre_3171_, lean_object* v_e_3172_, lean_object* v_post_3173_, uint8_t v_usedLetOnly_3174_, uint8_t v_skipConstInApp_3175_, uint8_t v_skipInstances_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_Lean_Core_checkSystem(v___x_3170_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v___x_3184_; 
lean_dec_ref_known(v___x_3183_, 1);
lean_inc_ref(v_pre_3171_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc_ref(v_e_3172_);
v___x_3184_ = lean_apply_6(v_pre_3171_, v_e_3172_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, lean_box(0));
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3233_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3233_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3233_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___y_3190_; 
switch(lean_obj_tag(v_a_3185_))
{
case 0:
{
lean_object* v_e_3225_; lean_object* v___x_3227_; 
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_e_3172_);
lean_dec_ref(v_pre_3171_);
v_e_3225_ = lean_ctor_get(v_a_3185_, 0);
lean_inc_ref(v_e_3225_);
lean_dec_ref_known(v_a_3185_, 1);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v_e_3225_);
v___x_3227_ = v___x_3187_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_e_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
case 1:
{
lean_object* v_e_3229_; lean_object* v___x_3230_; 
lean_del_object(v___x_3187_);
lean_dec_ref(v_e_3172_);
v_e_3229_ = lean_ctor_get(v_a_3185_, 0);
lean_inc_ref(v_e_3229_);
lean_dec_ref_known(v_a_3185_, 1);
v___x_3230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v_e_3229_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3230_;
}
default: 
{
lean_object* v_e_x3f_3231_; 
lean_del_object(v___x_3187_);
v_e_x3f_3231_ = lean_ctor_get(v_a_3185_, 0);
lean_inc(v_e_x3f_3231_);
lean_dec_ref_known(v_a_3185_, 1);
if (lean_obj_tag(v_e_x3f_3231_) == 0)
{
v___y_3190_ = v_e_3172_;
goto v___jp_3189_;
}
else
{
lean_object* v_val_3232_; 
lean_dec_ref(v_e_3172_);
v_val_3232_ = lean_ctor_get(v_e_x3f_3231_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v_e_x3f_3231_, 1);
v___y_3190_ = v_val_3232_;
goto v___jp_3189_;
}
}
}
v___jp_3189_:
{
switch(lean_obj_tag(v___y_3190_))
{
case 7:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___x_3191_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3192_;
}
case 6:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3194_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___x_3193_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3194_;
}
case 8:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3196_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___x_3195_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3196_;
}
case 5:
{
lean_object* v_dummy_3197_; lean_object* v_nargs_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_dummy_3197_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3198_ = l_Lean_Expr_getAppNumArgs(v___y_3190_);
lean_inc(v_nargs_3198_);
v___x_3199_ = lean_mk_array(v_nargs_3198_, v_dummy_3197_);
v___x_3200_ = lean_unsigned_to_nat(1u);
v___x_3201_ = lean_nat_sub(v_nargs_3198_, v___x_3200_);
lean_dec(v_nargs_3198_);
v___x_3202_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3176_, v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v___y_3190_, v___x_3199_, v___x_3201_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3202_;
}
case 10:
{
lean_object* v_data_3203_; lean_object* v_expr_3204_; lean_object* v___x_3205_; 
v_data_3203_ = lean_ctor_get(v___y_3190_, 0);
v_expr_3204_ = lean_ctor_get(v___y_3190_, 1);
lean_inc_ref(v_expr_3204_);
lean_inc_ref(v_post_3173_);
lean_inc_ref(v_pre_3171_);
v___x_3205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v_expr_3204_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; size_t v___x_3207_; size_t v___x_3208_; uint8_t v___x_3209_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v___x_3207_ = lean_ptr_addr(v_expr_3204_);
v___x_3208_ = lean_ptr_addr(v_a_3206_);
v___x_3209_ = lean_usize_dec_eq(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc(v_data_3203_);
lean_dec_ref_known(v___y_3190_, 2);
v___x_3210_ = l_Lean_Expr_mdata___override(v_data_3203_, v_a_3206_);
v___x_3211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___x_3210_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; 
lean_dec(v_a_3206_);
v___x_3212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3212_;
}
}
else
{
lean_dec_ref_known(v___y_3190_, 2);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3171_);
return v___x_3205_;
}
}
case 11:
{
lean_object* v_typeName_3213_; lean_object* v_idx_3214_; lean_object* v_struct_3215_; lean_object* v___x_3216_; 
v_typeName_3213_ = lean_ctor_get(v___y_3190_, 0);
v_idx_3214_ = lean_ctor_get(v___y_3190_, 1);
v_struct_3215_ = lean_ctor_get(v___y_3190_, 2);
lean_inc_ref(v_struct_3215_);
lean_inc_ref(v_post_3173_);
lean_inc_ref(v_pre_3171_);
v___x_3216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v_struct_3215_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; size_t v___x_3218_; size_t v___x_3219_; uint8_t v___x_3220_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v___x_3216_, 1);
v___x_3218_ = lean_ptr_addr(v_struct_3215_);
v___x_3219_ = lean_ptr_addr(v_a_3217_);
v___x_3220_ = lean_usize_dec_eq(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v_idx_3214_);
lean_inc(v_typeName_3213_);
lean_dec_ref_known(v___y_3190_, 3);
v___x_3221_ = l_Lean_Expr_proj___override(v_typeName_3213_, v_idx_3214_, v_a_3217_);
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___x_3221_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
lean_dec(v_a_3217_);
v___x_3223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3223_;
}
}
else
{
lean_dec_ref_known(v___y_3190_, 3);
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_pre_3171_);
return v___x_3216_;
}
}
default: 
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3171_, v_post_3173_, v_usedLetOnly_3174_, v_skipConstInApp_3175_, v_skipInstances_3176_, v___y_3190_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3224_;
}
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_e_3172_);
lean_dec_ref(v_pre_3171_);
v_a_3234_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3184_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3184_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_post_3173_);
lean_dec_ref(v_e_3172_);
lean_dec_ref(v_pre_3171_);
v_a_3242_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3183_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3183_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3250_, lean_object* v_pre_3251_, lean_object* v_e_3252_, lean_object* v_post_3253_, lean_object* v_usedLetOnly_3254_, lean_object* v_skipConstInApp_3255_, lean_object* v_skipInstances_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v_usedLetOnly_boxed_3263_; uint8_t v_skipConstInApp_boxed_3264_; uint8_t v_skipInstances_boxed_3265_; lean_object* v_res_3266_; 
v_usedLetOnly_boxed_3263_ = lean_unbox(v_usedLetOnly_3254_);
v_skipConstInApp_boxed_3264_ = lean_unbox(v_skipConstInApp_3255_);
v_skipInstances_boxed_3265_ = lean_unbox(v_skipInstances_3256_);
v_res_3266_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3250_, v_pre_3251_, v_e_3252_, v_post_3253_, v_usedLetOnly_boxed_3263_, v_skipConstInApp_boxed_3264_, v_skipInstances_boxed_3265_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3267_, lean_object* v_post_3268_, uint8_t v_usedLetOnly_3269_, uint8_t v_skipConstInApp_3270_, uint8_t v_skipInstances_3271_, lean_object* v_e_3272_, lean_object* v_a_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_inc(v_a_3273_);
v___x_3279_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3279_, 0, lean_box(0));
lean_closure_set(v___x_3279_, 1, lean_box(0));
lean_closure_set(v___x_3279_, 2, v_a_3273_);
v___x_3280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3279_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3315_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3315_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3315_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3281_, v_e_3272_);
lean_dec(v_a_3281_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; 
lean_del_object(v___x_3283_);
v___x_3286_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3287_ = lean_box(v_usedLetOnly_3269_);
v___x_3288_ = lean_box(v_skipConstInApp_3270_);
v___x_3289_ = lean_box(v_skipInstances_3271_);
lean_inc_ref(v_e_3272_);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3290_, 0, v___x_3286_);
lean_closure_set(v___f_3290_, 1, v_pre_3267_);
lean_closure_set(v___f_3290_, 2, v_e_3272_);
lean_closure_set(v___f_3290_, 3, v_post_3268_);
lean_closure_set(v___f_3290_, 4, v___x_3287_);
lean_closure_set(v___f_3290_, 5, v___x_3288_);
lean_closure_set(v___f_3290_, 6, v___x_3289_);
v___x_3291_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3290_, v_a_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc_n(v_a_3292_, 2);
lean_dec_ref_known(v___x_3291_, 1);
lean_inc(v_a_3273_);
v___f_3293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3293_, 0, v_a_3273_);
lean_closure_set(v___f_3293_, 1, v_e_3272_);
lean_closure_set(v___f_3293_, 2, v_a_3292_);
v___x_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3293_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3302_);
v___x_3296_ = v___x_3294_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3294_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v_a_3292_);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3292_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3292_);
v_a_3303_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3294_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3294_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_dec_ref(v_e_3272_);
return v___x_3291_;
}
}
else
{
lean_object* v_val_3311_; lean_object* v___x_3313_; 
lean_dec_ref(v_e_3272_);
lean_dec_ref(v_post_3268_);
lean_dec_ref(v_pre_3267_);
v_val_3311_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_val_3311_);
lean_dec_ref_known(v___x_3285_, 1);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_val_3311_);
v___x_3313_ = v___x_3283_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_val_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec_ref(v_e_3272_);
lean_dec_ref(v_post_3268_);
lean_dec_ref(v_pre_3267_);
v_a_3316_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3280_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3280_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3324_, lean_object* v_pre_3325_, lean_object* v_post_3326_, lean_object* v_usedLetOnly_3327_, lean_object* v_skipConstInApp_3328_, lean_object* v_skipInstances_3329_, lean_object* v_body_3330_, lean_object* v_x_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_usedLetOnly_boxed_3338_; uint8_t v_skipConstInApp_boxed_3339_; uint8_t v_skipInstances_boxed_3340_; lean_object* v_res_3341_; 
v_usedLetOnly_boxed_3338_ = lean_unbox(v_usedLetOnly_3327_);
v_skipConstInApp_boxed_3339_ = lean_unbox(v_skipConstInApp_3328_);
v_skipInstances_boxed_3340_ = lean_unbox(v_skipInstances_3329_);
v_res_3341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3324_, v_pre_3325_, v_post_3326_, v_usedLetOnly_boxed_3338_, v_skipConstInApp_boxed_3339_, v_skipInstances_boxed_3340_, v_body_3330_, v_x_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3342_, lean_object* v_post_3343_, uint8_t v_usedLetOnly_3344_, uint8_t v_skipConstInApp_3345_, uint8_t v_skipInstances_3346_, lean_object* v_fvars_3347_, lean_object* v_e_3348_, lean_object* v_a_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
if (lean_obj_tag(v_e_3348_) == 7)
{
lean_object* v_binderName_3355_; lean_object* v_binderType_3356_; lean_object* v_body_3357_; uint8_t v_binderInfo_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_binderName_3355_ = lean_ctor_get(v_e_3348_, 0);
lean_inc(v_binderName_3355_);
v_binderType_3356_ = lean_ctor_get(v_e_3348_, 1);
lean_inc_ref(v_binderType_3356_);
v_body_3357_ = lean_ctor_get(v_e_3348_, 2);
lean_inc_ref(v_body_3357_);
v_binderInfo_3358_ = lean_ctor_get_uint8(v_e_3348_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3348_, 3);
v___x_3359_ = lean_expr_instantiate_rev(v_binderType_3356_, v_fvars_3347_);
lean_dec_ref(v_binderType_3356_);
lean_inc_ref(v_post_3343_);
lean_inc_ref(v_pre_3342_);
v___x_3360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3342_, v_post_3343_, v_usedLetOnly_3344_, v_skipConstInApp_3345_, v_skipInstances_3346_, v___x_3359_, v_a_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___f_3365_; uint8_t v___x_3366_; lean_object* v___x_3367_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = lean_box(v_usedLetOnly_3344_);
v___x_3363_ = lean_box(v_skipConstInApp_3345_);
v___x_3364_ = lean_box(v_skipInstances_3346_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3365_, 0, v_fvars_3347_);
lean_closure_set(v___f_3365_, 1, v_pre_3342_);
lean_closure_set(v___f_3365_, 2, v_post_3343_);
lean_closure_set(v___f_3365_, 3, v___x_3362_);
lean_closure_set(v___f_3365_, 4, v___x_3363_);
lean_closure_set(v___f_3365_, 5, v___x_3364_);
lean_closure_set(v___f_3365_, 6, v_body_3357_);
v___x_3366_ = 0;
v___x_3367_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3355_, v_binderInfo_3358_, v_a_3361_, v___f_3365_, v___x_3366_, v_a_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
return v___x_3367_;
}
else
{
lean_dec_ref(v_body_3357_);
lean_dec(v_binderName_3355_);
lean_dec_ref(v_fvars_3347_);
lean_dec_ref(v_post_3343_);
lean_dec_ref(v_pre_3342_);
return v___x_3360_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_expr_instantiate_rev(v_e_3348_, v_fvars_3347_);
lean_dec_ref(v_e_3348_);
lean_inc_ref(v_post_3343_);
lean_inc_ref(v_pre_3342_);
v___x_3369_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3342_, v_post_3343_, v_usedLetOnly_3344_, v_skipConstInApp_3345_, v_skipInstances_3346_, v___x_3368_, v_a_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; uint8_t v___x_3371_; uint8_t v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v___x_3371_ = 0;
v___x_3372_ = 1;
v___x_3373_ = 1;
v___x_3374_ = l_Lean_Meta_mkForallFVars(v_fvars_3347_, v_a_3370_, v___x_3371_, v_usedLetOnly_3344_, v___x_3372_, v___x_3373_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec_ref(v_fvars_3347_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3342_, v_post_3343_, v_usedLetOnly_3344_, v_skipConstInApp_3345_, v_skipInstances_3346_, v_a_3375_, v_a_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
return v___x_3376_;
}
else
{
lean_dec_ref(v_post_3343_);
lean_dec_ref(v_pre_3342_);
return v___x_3374_;
}
}
else
{
lean_dec_ref(v_fvars_3347_);
lean_dec_ref(v_post_3343_);
lean_dec_ref(v_pre_3342_);
return v___x_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3377_, lean_object* v_pre_3378_, lean_object* v_post_3379_, uint8_t v_usedLetOnly_3380_, uint8_t v_skipConstInApp_3381_, uint8_t v_skipInstances_3382_, lean_object* v_body_3383_, lean_object* v_x_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = lean_array_push(v_fvars_3377_, v_x_3384_);
v___x_3392_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3378_, v_post_3379_, v_usedLetOnly_3380_, v_skipConstInApp_3381_, v_skipInstances_3382_, v___x_3391_, v_body_3383_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3393_, lean_object* v_post_3394_, lean_object* v_usedLetOnly_3395_, lean_object* v_skipConstInApp_3396_, lean_object* v_skipInstances_3397_, lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
uint8_t v_usedLetOnly_boxed_3405_; uint8_t v_skipConstInApp_boxed_3406_; uint8_t v_skipInstances_boxed_3407_; lean_object* v_res_3408_; 
v_usedLetOnly_boxed_3405_ = lean_unbox(v_usedLetOnly_3395_);
v_skipConstInApp_boxed_3406_ = lean_unbox(v_skipConstInApp_3396_);
v_skipInstances_boxed_3407_ = lean_unbox(v_skipInstances_3397_);
v_res_3408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3393_, v_post_3394_, v_usedLetOnly_boxed_3405_, v_skipConstInApp_boxed_3406_, v_skipInstances_boxed_3407_, v_e_3398_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v_a_3399_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3409_, lean_object* v_post_3410_, lean_object* v_usedLetOnly_3411_, lean_object* v_skipConstInApp_3412_, lean_object* v_skipInstances_3413_, lean_object* v_sz_3414_, lean_object* v_i_3415_, lean_object* v_bs_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
uint8_t v_usedLetOnly_boxed_3423_; uint8_t v_skipConstInApp_boxed_3424_; uint8_t v_skipInstances_boxed_3425_; size_t v_sz_boxed_3426_; size_t v_i_boxed_3427_; lean_object* v_res_3428_; 
v_usedLetOnly_boxed_3423_ = lean_unbox(v_usedLetOnly_3411_);
v_skipConstInApp_boxed_3424_ = lean_unbox(v_skipConstInApp_3412_);
v_skipInstances_boxed_3425_ = lean_unbox(v_skipInstances_3413_);
v_sz_boxed_3426_ = lean_unbox_usize(v_sz_3414_);
lean_dec(v_sz_3414_);
v_i_boxed_3427_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_res_3428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3409_, v_post_3410_, v_usedLetOnly_boxed_3423_, v_skipConstInApp_boxed_3424_, v_skipInstances_boxed_3425_, v_sz_boxed_3426_, v_i_boxed_3427_, v_bs_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3429_, lean_object* v_post_3430_, lean_object* v_usedLetOnly_3431_, lean_object* v_skipConstInApp_3432_, lean_object* v_skipInstances_3433_, lean_object* v_e_3434_, lean_object* v_a_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v_usedLetOnly_boxed_3441_; uint8_t v_skipConstInApp_boxed_3442_; uint8_t v_skipInstances_boxed_3443_; lean_object* v_res_3444_; 
v_usedLetOnly_boxed_3441_ = lean_unbox(v_usedLetOnly_3431_);
v_skipConstInApp_boxed_3442_ = lean_unbox(v_skipConstInApp_3432_);
v_skipInstances_boxed_3443_ = lean_unbox(v_skipInstances_3433_);
v_res_3444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3429_, v_post_3430_, v_usedLetOnly_boxed_3441_, v_skipConstInApp_boxed_3442_, v_skipInstances_boxed_3443_, v_e_3434_, v_a_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v_a_3435_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3445_, lean_object* v_post_3446_, lean_object* v_usedLetOnly_3447_, lean_object* v_skipConstInApp_3448_, lean_object* v_skipInstances_3449_, lean_object* v_fvars_3450_, lean_object* v_e_3451_, lean_object* v_a_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v_usedLetOnly_boxed_3458_; uint8_t v_skipConstInApp_boxed_3459_; uint8_t v_skipInstances_boxed_3460_; lean_object* v_res_3461_; 
v_usedLetOnly_boxed_3458_ = lean_unbox(v_usedLetOnly_3447_);
v_skipConstInApp_boxed_3459_ = lean_unbox(v_skipConstInApp_3448_);
v_skipInstances_boxed_3460_ = lean_unbox(v_skipInstances_3449_);
v_res_3461_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3445_, v_post_3446_, v_usedLetOnly_boxed_3458_, v_skipConstInApp_boxed_3459_, v_skipInstances_boxed_3460_, v_fvars_3450_, v_e_3451_, v_a_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v_a_3452_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3462_, lean_object* v_post_3463_, lean_object* v_usedLetOnly_3464_, lean_object* v_skipConstInApp_3465_, lean_object* v_skipInstances_3466_, lean_object* v_fvars_3467_, lean_object* v_e_3468_, lean_object* v_a_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v_usedLetOnly_boxed_3475_; uint8_t v_skipConstInApp_boxed_3476_; uint8_t v_skipInstances_boxed_3477_; lean_object* v_res_3478_; 
v_usedLetOnly_boxed_3475_ = lean_unbox(v_usedLetOnly_3464_);
v_skipConstInApp_boxed_3476_ = lean_unbox(v_skipConstInApp_3465_);
v_skipInstances_boxed_3477_ = lean_unbox(v_skipInstances_3466_);
v_res_3478_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3462_, v_post_3463_, v_usedLetOnly_boxed_3475_, v_skipConstInApp_boxed_3476_, v_skipInstances_boxed_3477_, v_fvars_3467_, v_e_3468_, v_a_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v_a_3469_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3479_, lean_object* v_post_3480_, lean_object* v_usedLetOnly_3481_, lean_object* v_skipConstInApp_3482_, lean_object* v_skipInstances_3483_, lean_object* v_fvars_3484_, lean_object* v_e_3485_, lean_object* v_a_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
uint8_t v_usedLetOnly_boxed_3492_; uint8_t v_skipConstInApp_boxed_3493_; uint8_t v_skipInstances_boxed_3494_; lean_object* v_res_3495_; 
v_usedLetOnly_boxed_3492_ = lean_unbox(v_usedLetOnly_3481_);
v_skipConstInApp_boxed_3493_ = lean_unbox(v_skipConstInApp_3482_);
v_skipInstances_boxed_3494_ = lean_unbox(v_skipInstances_3483_);
v_res_3495_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3479_, v_post_3480_, v_usedLetOnly_boxed_3492_, v_skipConstInApp_boxed_3493_, v_skipInstances_boxed_3494_, v_fvars_3484_, v_e_3485_, v_a_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v_a_3486_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3496_, lean_object* v___x_3497_, lean_object* v_pre_3498_, lean_object* v_post_3499_, lean_object* v_usedLetOnly_3500_, lean_object* v_skipConstInApp_3501_, lean_object* v_skipInstances_3502_, lean_object* v_a_3503_, lean_object* v_b_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v_usedLetOnly_boxed_3511_; uint8_t v_skipConstInApp_boxed_3512_; uint8_t v_skipInstances_boxed_3513_; lean_object* v_res_3514_; 
v_usedLetOnly_boxed_3511_ = lean_unbox(v_usedLetOnly_3500_);
v_skipConstInApp_boxed_3512_ = lean_unbox(v_skipConstInApp_3501_);
v_skipInstances_boxed_3513_ = lean_unbox(v_skipInstances_3502_);
v_res_3514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3496_, v___x_3497_, v_pre_3498_, v_post_3499_, v_usedLetOnly_boxed_3511_, v_skipConstInApp_boxed_3512_, v_skipInstances_boxed_3513_, v_a_3503_, v_b_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___x_3497_);
lean_dec(v_upperBound_3496_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3515_, lean_object* v_pre_3516_, lean_object* v_post_3517_, lean_object* v_usedLetOnly_3518_, lean_object* v_skipConstInApp_3519_, lean_object* v_x_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
uint8_t v_skipInstances_boxed_3529_; uint8_t v_usedLetOnly_boxed_3530_; uint8_t v_skipConstInApp_boxed_3531_; lean_object* v_res_3532_; 
v_skipInstances_boxed_3529_ = lean_unbox(v_skipInstances_3515_);
v_usedLetOnly_boxed_3530_ = lean_unbox(v_usedLetOnly_3518_);
v_skipConstInApp_boxed_3531_ = lean_unbox(v_skipConstInApp_3519_);
v_res_3532_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3529_, v_pre_3516_, v_post_3517_, v_usedLetOnly_boxed_3530_, v_skipConstInApp_boxed_3531_, v_x_3520_, v_x_3521_, v_x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
return v_res_3532_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_unsigned_to_nat(16u);
v___x_3535_ = lean_mk_array(v___x_3534_, v___x_3533_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
lean_ctor_set(v___x_3538_, 1, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3540_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3540_, 0, lean_box(0));
lean_closure_set(v___x_3540_, 1, lean_box(0));
lean_closure_set(v___x_3540_, 2, v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3541_, lean_object* v_pre_3542_, lean_object* v_post_3543_, uint8_t v_usedLetOnly_3544_, uint8_t v_skipConstInApp_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v_a_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3551_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3552_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3551_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = 0;
v___x_3555_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3542_, v_post_3543_, v_usedLetOnly_3544_, v_skipConstInApp_3545_, v___x_3554_, v_input_3541_, v_a_3553_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3557_, 0, lean_box(0));
lean_closure_set(v___x_3557_, 1, lean_box(0));
lean_closure_set(v___x_3557_, 2, v_a_3553_);
v___x_3558_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3557_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3566_);
v___x_3560_ = v___x_3558_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_a_3556_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3556_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_dec(v_a_3553_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3567_, lean_object* v_pre_3568_, lean_object* v_post_3569_, lean_object* v_usedLetOnly_3570_, lean_object* v_skipConstInApp_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
uint8_t v_usedLetOnly_boxed_3577_; uint8_t v_skipConstInApp_boxed_3578_; lean_object* v_res_3579_; 
v_usedLetOnly_boxed_3577_ = lean_unbox(v_usedLetOnly_3570_);
v_skipConstInApp_boxed_3578_ = lean_unbox(v_skipConstInApp_3571_);
v_res_3579_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3567_, v_pre_3568_, v_post_3569_, v_usedLetOnly_boxed_3577_, v_skipConstInApp_boxed_3578_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3581_, lean_object* v_p_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; uint8_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3588_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3581_, v_a_3584_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___f_3590_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3591_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3591_, 0, v_p_3582_);
v___x_3592_ = 0;
v___x_3593_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3589_, v___f_3590_, v___f_3591_, v___x_3592_, v___x_3592_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3594_, lean_object* v_p_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_etaStructReduce(v_e_3594_, v_p_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3602_, lean_object* v___x_3603_, lean_object* v_pre_3604_, lean_object* v_post_3605_, uint8_t v_usedLetOnly_3606_, uint8_t v_skipConstInApp_3607_, uint8_t v_skipInstances_3608_, lean_object* v___x_3609_, lean_object* v_inst_3610_, lean_object* v_R_3611_, lean_object* v_a_3612_, lean_object* v_b_3613_, lean_object* v_c_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3602_, v___x_3603_, v_pre_3604_, v_post_3605_, v_usedLetOnly_3606_, v_skipConstInApp_3607_, v_skipInstances_3608_, v_a_3612_, v_b_3613_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3622_ = _args[0];
lean_object* v___x_3623_ = _args[1];
lean_object* v_pre_3624_ = _args[2];
lean_object* v_post_3625_ = _args[3];
lean_object* v_usedLetOnly_3626_ = _args[4];
lean_object* v_skipConstInApp_3627_ = _args[5];
lean_object* v_skipInstances_3628_ = _args[6];
lean_object* v___x_3629_ = _args[7];
lean_object* v_inst_3630_ = _args[8];
lean_object* v_R_3631_ = _args[9];
lean_object* v_a_3632_ = _args[10];
lean_object* v_b_3633_ = _args[11];
lean_object* v_c_3634_ = _args[12];
lean_object* v___y_3635_ = _args[13];
lean_object* v___y_3636_ = _args[14];
lean_object* v___y_3637_ = _args[15];
lean_object* v___y_3638_ = _args[16];
lean_object* v___y_3639_ = _args[17];
lean_object* v___y_3640_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3641_; uint8_t v_skipConstInApp_boxed_3642_; uint8_t v_skipInstances_boxed_3643_; lean_object* v_res_3644_; 
v_usedLetOnly_boxed_3641_ = lean_unbox(v_usedLetOnly_3626_);
v_skipConstInApp_boxed_3642_ = lean_unbox(v_skipConstInApp_3627_);
v_skipInstances_boxed_3643_ = lean_unbox(v_skipInstances_3628_);
v_res_3644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3622_, v___x_3623_, v_pre_3624_, v_post_3625_, v_usedLetOnly_boxed_3641_, v_skipConstInApp_boxed_3642_, v_skipInstances_boxed_3643_, v___x_3629_, v_inst_3630_, v_R_3631_, v_a_3632_, v_b_3633_, v_c_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec(v___x_3629_);
lean_dec_ref(v___x_3623_);
lean_dec(v_upperBound_3622_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3645_, lean_object* v_m_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3646_, v_a_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3649_, lean_object* v_m_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3649_, v_m_3650_, v_a_3651_);
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_m_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3653_, lean_object* v_name_3654_, uint8_t v_bi_3655_, lean_object* v_type_3656_, lean_object* v_k_3657_, uint8_t v_kind_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3654_, v_bi_3655_, v_type_3656_, v_k_3657_, v_kind_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_name_3667_, lean_object* v_bi_3668_, lean_object* v_type_3669_, lean_object* v_k_3670_, lean_object* v_kind_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v_bi_boxed_3678_; uint8_t v_kind_boxed_3679_; lean_object* v_res_3680_; 
v_bi_boxed_3678_ = lean_unbox(v_bi_3668_);
v_kind_boxed_3679_ = lean_unbox(v_kind_3671_);
v_res_3680_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3666_, v_name_3667_, v_bi_boxed_3678_, v_type_3669_, v_k_3670_, v_kind_boxed_3679_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3681_, lean_object* v_name_3682_, lean_object* v_type_3683_, lean_object* v_val_3684_, lean_object* v_k_3685_, uint8_t v_nondep_3686_, uint8_t v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3682_, v_type_3683_, v_val_3684_, v_k_3685_, v_nondep_3686_, v_kind_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3695_, lean_object* v_name_3696_, lean_object* v_type_3697_, lean_object* v_val_3698_, lean_object* v_k_3699_, lean_object* v_nondep_3700_, lean_object* v_kind_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v_nondep_boxed_3708_; uint8_t v_kind_boxed_3709_; lean_object* v_res_3710_; 
v_nondep_boxed_3708_ = lean_unbox(v_nondep_3700_);
v_kind_boxed_3709_ = lean_unbox(v_kind_3701_);
v_res_3710_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3695_, v_name_3696_, v_type_3697_, v_val_3698_, v_k_3699_, v_nondep_boxed_3708_, v_kind_boxed_3709_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3711_, lean_object* v_ref_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3712_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3719_, lean_object* v_ref_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3719_, v_ref_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3727_, lean_object* v_x_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3736_, lean_object* v_x_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3736_, v_x_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3745_, lean_object* v_m_3746_, lean_object* v_a_3747_, lean_object* v_b_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3746_, v_a_3747_, v_b_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3750_, lean_object* v_a_3751_, lean_object* v_x_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3751_, v_x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3754_, lean_object* v_a_3755_, lean_object* v_x_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3754_, v_a_3755_, v_x_3756_);
lean_dec(v_x_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3757_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3758_, lean_object* v_a_3759_, lean_object* v_x_3760_){
_start:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3759_, v_x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3762_, lean_object* v_a_3763_, lean_object* v_x_3764_){
_start:
{
uint8_t v_res_3765_; lean_object* v_r_3766_; 
v_res_3765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3762_, v_a_3763_, v_x_3764_);
lean_dec(v_x_3764_);
lean_dec_ref(v_a_3763_);
v_r_3766_ = lean_box(v_res_3765_);
return v_r_3766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3767_, lean_object* v_data_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3770_, lean_object* v_a_3771_, lean_object* v_b_3772_, lean_object* v_x_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3771_, v_b_3772_, v_x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3775_, lean_object* v_i_3776_, lean_object* v_source_3777_, lean_object* v_target_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3776_, v_source_3777_, v_target_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3781_, v_x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3784_, lean_object* v_inst_3785_, lean_object* v_toBind_3786_, lean_object* v___f_3787_, lean_object* v_____do__lift_3788_){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3789_, 0, v_____do__lift_3788_);
lean_closure_set(v___x_3789_, 1, v_binderType_3784_);
v___x_3790_ = lean_apply_2(v_inst_3785_, lean_box(0), v___x_3789_);
v___x_3791_ = lean_apply_4(v_toBind_3786_, lean_box(0), lean_box(0), v___x_3790_, v___f_3787_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3792_, lean_object* v_usedFields_3793_, lean_object* v_binderName_3794_, lean_object* v_body_3795_, lean_object* v_val_3796_, lean_object* v_inst_3797_, lean_object* v_inst_3798_, lean_object* v_fieldVal_x3f_3799_, lean_object* v_____do__lift_3800_){
_start:
{
uint8_t v_____do__lift_469__boxed_3801_; lean_object* v_res_3802_; 
v_____do__lift_469__boxed_3801_ = lean_unbox(v_____do__lift_3800_);
v_res_3802_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3792_, v_usedFields_3793_, v_binderName_3794_, v_body_3795_, v_val_3796_, v_inst_3797_, v_inst_3798_, v_fieldVal_x3f_3799_, v_____do__lift_469__boxed_3801_);
lean_dec_ref(v_val_3796_);
lean_dec_ref(v_body_3795_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3803_, lean_object* v_usedFields_3804_, lean_object* v_binderName_3805_, lean_object* v_body_3806_, lean_object* v_inst_3807_, lean_object* v_inst_3808_, lean_object* v_fieldVal_x3f_3809_, lean_object* v_binderType_3810_, lean_object* v_toBind_3811_, lean_object* v_____x_3812_){
_start:
{
if (lean_obj_tag(v_____x_3812_) == 1)
{
lean_object* v_val_3813_; lean_object* v___f_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v_val_3813_ = lean_ctor_get(v_____x_3812_, 0);
lean_inc_n(v_val_3813_, 2);
lean_dec_ref_known(v_____x_3812_, 1);
lean_inc_n(v_inst_3808_, 2);
v___f_3814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3814_, 0, v_toPure_3803_);
lean_closure_set(v___f_3814_, 1, v_usedFields_3804_);
lean_closure_set(v___f_3814_, 2, v_binderName_3805_);
lean_closure_set(v___f_3814_, 3, v_body_3806_);
lean_closure_set(v___f_3814_, 4, v_val_3813_);
lean_closure_set(v___f_3814_, 5, v_inst_3807_);
lean_closure_set(v___f_3814_, 6, v_inst_3808_);
lean_closure_set(v___f_3814_, 7, v_fieldVal_x3f_3809_);
lean_inc(v_toBind_3811_);
v___f_3815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3815_, 0, v_binderType_3810_);
lean_closure_set(v___f_3815_, 1, v_inst_3808_);
lean_closure_set(v___f_3815_, 2, v_toBind_3811_);
lean_closure_set(v___f_3815_, 3, v___f_3814_);
v___x_3816_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3816_, 0, v_val_3813_);
v___x_3817_ = lean_apply_2(v_inst_3808_, lean_box(0), v___x_3816_);
v___x_3818_ = lean_apply_4(v_toBind_3811_, lean_box(0), lean_box(0), v___x_3817_, v___f_3815_);
return v___x_3818_;
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_dec(v_____x_3812_);
lean_dec(v_toBind_3811_);
lean_dec_ref(v_binderType_3810_);
lean_dec(v_fieldVal_x3f_3809_);
lean_dec(v_inst_3808_);
lean_dec_ref(v_inst_3807_);
lean_dec_ref(v_body_3806_);
lean_dec(v_binderName_3805_);
lean_dec(v_usedFields_3804_);
v___x_3819_ = lean_box(0);
v___x_3820_ = lean_apply_2(v_toPure_3803_, lean_box(0), v___x_3819_);
return v___x_3820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3824_, lean_object* v_inst_3825_, lean_object* v_fieldVal_x3f_3826_, lean_object* v_usedFields_3827_, lean_object* v_e_3828_){
_start:
{
lean_object* v_toApplicative_3829_; lean_object* v_toBind_3830_; lean_object* v_toPure_3831_; 
v_toApplicative_3829_ = lean_ctor_get(v_inst_3824_, 0);
v_toBind_3830_ = lean_ctor_get(v_inst_3824_, 1);
v_toPure_3831_ = lean_ctor_get(v_toApplicative_3829_, 1);
lean_inc(v_toPure_3831_);
if (lean_obj_tag(v_e_3828_) == 6)
{
lean_object* v_binderName_3836_; lean_object* v_binderType_3837_; lean_object* v_body_3838_; lean_object* v___f_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_inc_n(v_toBind_3830_, 2);
v_binderName_3836_ = lean_ctor_get(v_e_3828_, 0);
lean_inc_n(v_binderName_3836_, 2);
v_binderType_3837_ = lean_ctor_get(v_e_3828_, 1);
lean_inc_ref(v_binderType_3837_);
v_body_3838_ = lean_ctor_get(v_e_3828_, 2);
lean_inc_ref(v_body_3838_);
lean_dec_ref_known(v_e_3828_, 3);
lean_inc(v_fieldVal_x3f_3826_);
v___f_3839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3839_, 0, v_toPure_3831_);
lean_closure_set(v___f_3839_, 1, v_usedFields_3827_);
lean_closure_set(v___f_3839_, 2, v_binderName_3836_);
lean_closure_set(v___f_3839_, 3, v_body_3838_);
lean_closure_set(v___f_3839_, 4, v_inst_3824_);
lean_closure_set(v___f_3839_, 5, v_inst_3825_);
lean_closure_set(v___f_3839_, 6, v_fieldVal_x3f_3826_);
lean_closure_set(v___f_3839_, 7, v_binderType_3837_);
lean_closure_set(v___f_3839_, 8, v_toBind_3830_);
v___x_3840_ = lean_apply_1(v_fieldVal_x3f_3826_, v_binderName_3836_);
v___x_3841_ = lean_apply_4(v_toBind_3830_, lean_box(0), lean_box(0), v___x_3840_, v___f_3839_);
return v___x_3841_;
}
else
{
lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_fieldVal_x3f_3826_);
lean_dec(v_inst_3825_);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_inst_3824_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; lean_object* v_unused_3860_; 
v_unused_3859_ = lean_ctor_get(v_inst_3824_, 1);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_inst_3824_, 0);
lean_dec(v_unused_3860_);
v___x_3843_ = v_inst_3824_;
v_isShared_3844_ = v_isSharedCheck_3858_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v_inst_3824_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3858_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; uint8_t v___x_3846_; 
lean_inc_ref(v_e_3828_);
v___x_3845_ = l_Lean_Expr_cleanupAnnotations(v_e_3828_);
v___x_3846_ = l_Lean_Expr_isApp(v___x_3845_);
if (v___x_3846_ == 0)
{
lean_dec_ref(v___x_3845_);
lean_del_object(v___x_3843_);
goto v___jp_3832_;
}
else
{
lean_object* v_arg_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_arg_3847_ = lean_ctor_get(v___x_3845_, 1);
lean_inc_ref(v_arg_3847_);
v___x_3848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3845_);
v___x_3849_ = l_Lean_Expr_isApp(v___x_3848_);
if (v___x_3849_ == 0)
{
lean_dec_ref(v___x_3848_);
lean_dec_ref(v_arg_3847_);
lean_del_object(v___x_3843_);
goto v___jp_3832_;
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3848_);
v___x_3851_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3852_ = l_Lean_Expr_isConstOf(v___x_3850_, v___x_3851_);
lean_dec_ref(v___x_3850_);
if (v___x_3852_ == 0)
{
lean_dec_ref(v_arg_3847_);
lean_del_object(v___x_3843_);
goto v___jp_3832_;
}
else
{
lean_object* v___x_3854_; 
lean_dec_ref(v_e_3828_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v_arg_3847_);
lean_ctor_set(v___x_3843_, 0, v_usedFields_3827_);
v___x_3854_ = v___x_3843_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_usedFields_3827_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_arg_3847_);
v___x_3854_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
v___x_3856_ = lean_apply_2(v_toPure_3831_, lean_box(0), v___x_3855_);
return v___x_3856_;
}
}
}
}
}
}
v___jp_3832_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v_usedFields_3827_);
lean_ctor_set(v___x_3833_, 1, v_e_3828_);
v___x_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
v___x_3835_ = lean_apply_2(v_toPure_3831_, lean_box(0), v___x_3834_);
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3861_, lean_object* v_usedFields_3862_, lean_object* v_binderName_3863_, lean_object* v_body_3864_, lean_object* v_val_3865_, lean_object* v_inst_3866_, lean_object* v_inst_3867_, lean_object* v_fieldVal_x3f_3868_, uint8_t v_____do__lift_3869_){
_start:
{
if (v_____do__lift_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec(v_fieldVal_x3f_3868_);
lean_dec(v_inst_3867_);
lean_dec_ref(v_inst_3866_);
lean_dec(v_binderName_3863_);
lean_dec(v_usedFields_3862_);
v___x_3870_ = lean_box(0);
v___x_3871_ = lean_apply_2(v_toPure_3861_, lean_box(0), v___x_3870_);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v_toPure_3861_);
v___x_3872_ = l_Lean_NameSet_insert(v_usedFields_3862_, v_binderName_3863_);
v___x_3873_ = lean_expr_instantiate1(v_body_3864_, v_val_3865_);
v___x_3874_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3866_, v_inst_3867_, v_fieldVal_x3f_3868_, v___x_3872_, v___x_3873_);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3875_, lean_object* v_inst_3876_, lean_object* v_inst_3877_, lean_object* v_fieldVal_x3f_3878_, lean_object* v_usedFields_3879_, lean_object* v_e_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3876_, v_inst_3877_, v_fieldVal_x3f_3878_, v_usedFields_3879_, v_e_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3882_, lean_object* v_inst_3883_, lean_object* v_fieldVal_x3f_3884_, lean_object* v_toPure_3885_, lean_object* v_____s_3886_){
_start:
{
lean_object* v_fst_3887_; 
v_fst_3887_ = lean_ctor_get(v_____s_3886_, 0);
if (lean_obj_tag(v_fst_3887_) == 0)
{
lean_object* v_snd_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_dec(v_toPure_3885_);
v_snd_3888_ = lean_ctor_get(v_____s_3886_, 1);
lean_inc(v_snd_3888_);
lean_dec_ref(v_____s_3886_);
v___x_3889_ = l_Lean_NameSet_empty;
v___x_3890_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3882_, v_inst_3883_, v_fieldVal_x3f_3884_, v___x_3889_, v_snd_3888_);
return v___x_3890_;
}
else
{
lean_object* v_val_3891_; lean_object* v___x_3892_; 
lean_inc_ref(v_fst_3887_);
lean_dec_ref(v_____s_3886_);
lean_dec(v_fieldVal_x3f_3884_);
lean_dec(v_inst_3883_);
lean_dec_ref(v_inst_3882_);
v_val_3891_ = lean_ctor_get(v_fst_3887_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v_fst_3887_, 1);
v___x_3892_ = lean_apply_2(v_toPure_3885_, lean_box(0), v_val_3891_);
return v___x_3892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3893_, lean_object* v_a_3894_, lean_object* v___x_3895_, lean_object* v_toPure_3896_, lean_object* v_____r_3897_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = lean_expr_instantiate1(v_body_3893_, v_a_3894_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3895_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
v___x_3901_ = lean_apply_2(v_toPure_3896_, lean_box(0), v___x_3900_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3902_, lean_object* v_a_3903_, lean_object* v___x_3904_, lean_object* v_toPure_3905_, lean_object* v_____r_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3902_, v_a_3903_, v___x_3904_, v_toPure_3905_, v_____r_3906_);
lean_dec_ref(v_a_3903_);
lean_dec_ref(v_body_3902_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3910_, lean_object* v_toPure_3911_, lean_object* v___f_3912_, uint8_t v_____do__lift_3913_){
_start:
{
if (v_____do__lift_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec(v___f_3912_);
v___x_3914_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v_snd_3910_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v___x_3917_ = lean_apply_2(v_toPure_3911_, lean_box(0), v___x_3916_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec(v_toPure_3911_);
lean_dec(v_snd_3910_);
v___x_3918_ = lean_box(0);
v___x_3919_ = lean_apply_1(v___f_3912_, v___x_3918_);
return v___x_3919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3920_, lean_object* v_toPure_3921_, lean_object* v___f_3922_, lean_object* v_____do__lift_3923_){
_start:
{
uint8_t v_____do__lift_852__boxed_3924_; lean_object* v_res_3925_; 
v_____do__lift_852__boxed_3924_ = lean_unbox(v_____do__lift_3923_);
v_res_3925_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3920_, v_toPure_3921_, v___f_3922_, v_____do__lift_852__boxed_3924_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3926_, lean_object* v_inst_3927_, lean_object* v_toBind_3928_, lean_object* v___f_3929_, lean_object* v_____do__lift_3930_){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3931_, 0, v_____do__lift_3930_);
lean_closure_set(v___x_3931_, 1, v_binderType_3926_);
v___x_3932_ = lean_apply_2(v_inst_3927_, lean_box(0), v___x_3931_);
v___x_3933_ = lean_apply_4(v_toBind_3928_, lean_box(0), lean_box(0), v___x_3932_, v___f_3929_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3934_, lean_object* v_toPure_3935_, lean_object* v_levels_x3f_3936_, uint8_t v___x_3937_, lean_object* v_inst_3938_, lean_object* v_toBind_3939_, lean_object* v_a_3940_, lean_object* v_x_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_snd_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3964_; 
v_snd_3943_ = lean_ctor_get(v___y_3942_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___y_3942_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___y_3942_, 0);
lean_dec(v_unused_3965_);
v___x_3945_ = v___y_3942_;
v_isShared_3946_ = v_isSharedCheck_3964_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snd_3943_);
lean_dec(v___y_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3964_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
if (lean_obj_tag(v_snd_3943_) == 6)
{
lean_object* v_binderType_3947_; lean_object* v_body_3948_; lean_object* v___f_3949_; 
lean_del_object(v___x_3945_);
v_binderType_3947_ = lean_ctor_get(v_snd_3943_, 1);
lean_inc_ref(v_binderType_3947_);
v_body_3948_ = lean_ctor_get(v_snd_3943_, 2);
lean_inc(v_toPure_3935_);
lean_inc(v___x_3934_);
lean_inc_ref(v_a_3940_);
lean_inc_ref(v_body_3948_);
v___f_3949_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3949_, 0, v_body_3948_);
lean_closure_set(v___f_3949_, 1, v_a_3940_);
lean_closure_set(v___f_3949_, 2, v___x_3934_);
lean_closure_set(v___f_3949_, 3, v_toPure_3935_);
if (lean_obj_tag(v_levels_x3f_3936_) == 0)
{
if (v___x_3937_ == 0)
{
lean_inc_ref(v_body_3948_);
lean_dec_ref(v___f_3949_);
lean_dec_ref(v_binderType_3947_);
lean_dec_ref_known(v_snd_3943_, 3);
lean_dec(v_toBind_3939_);
lean_dec(v_inst_3938_);
goto v___jp_3950_;
}
else
{
lean_object* v___f_3953_; lean_object* v___f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
lean_dec(v___x_3934_);
v___f_3953_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3953_, 0, v_snd_3943_);
lean_closure_set(v___f_3953_, 1, v_toPure_3935_);
lean_closure_set(v___f_3953_, 2, v___f_3949_);
lean_inc(v_toBind_3939_);
lean_inc(v_inst_3938_);
v___f_3954_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3954_, 0, v_binderType_3947_);
lean_closure_set(v___f_3954_, 1, v_inst_3938_);
lean_closure_set(v___f_3954_, 2, v_toBind_3939_);
lean_closure_set(v___f_3954_, 3, v___f_3953_);
v___x_3955_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3955_, 0, v_a_3940_);
v___x_3956_ = lean_apply_2(v_inst_3938_, lean_box(0), v___x_3955_);
v___x_3957_ = lean_apply_4(v_toBind_3939_, lean_box(0), lean_box(0), v___x_3956_, v___f_3954_);
return v___x_3957_;
}
}
else
{
lean_inc_ref(v_body_3948_);
lean_dec_ref(v___f_3949_);
lean_dec_ref(v_binderType_3947_);
lean_dec_ref_known(v_snd_3943_, 3);
lean_dec(v_toBind_3939_);
lean_dec(v_inst_3938_);
goto v___jp_3950_;
}
v___jp_3950_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_box(0);
v___x_3952_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3948_, v_a_3940_, v___x_3934_, v_toPure_3935_, v___x_3951_);
lean_dec_ref(v_a_3940_);
lean_dec_ref(v_body_3948_);
return v___x_3952_;
}
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
lean_dec_ref(v_a_3940_);
lean_dec(v_toBind_3939_);
lean_dec(v_inst_3938_);
lean_dec(v___x_3934_);
v___x_3958_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3958_);
v___x_3960_ = v___x_3945_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_snd_3943_);
v___x_3960_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v___x_3962_ = lean_apply_2(v_toPure_3935_, lean_box(0), v___x_3961_);
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3966_, lean_object* v_toPure_3967_, lean_object* v_levels_x3f_3968_, lean_object* v___x_3969_, lean_object* v_inst_3970_, lean_object* v_toBind_3971_, lean_object* v_a_3972_, lean_object* v_x_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___x_888__boxed_3975_; lean_object* v_res_3976_; 
v___x_888__boxed_3975_ = lean_unbox(v___x_3969_);
v_res_3976_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3966_, v_toPure_3967_, v_levels_x3f_3968_, v___x_888__boxed_3975_, v_inst_3970_, v_toBind_3971_, v_a_3972_, v_x_3973_, v___y_3974_);
lean_dec(v_levels_x3f_3968_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3977_, lean_object* v_levels_x3f_3978_, uint8_t v___x_3979_, lean_object* v_inst_3980_, lean_object* v_toBind_3981_, lean_object* v_params_3982_, lean_object* v_inst_3983_, lean_object* v___f_3984_, lean_object* v_val_3985_){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; size_t v_sz_3990_; size_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3986_ = lean_box(0);
v___x_3987_ = lean_box(v___x_3979_);
lean_inc(v_toBind_3981_);
v___f_3988_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_3988_, 0, v___x_3986_);
lean_closure_set(v___f_3988_, 1, v_toPure_3977_);
lean_closure_set(v___f_3988_, 2, v_levels_x3f_3978_);
lean_closure_set(v___f_3988_, 3, v___x_3987_);
lean_closure_set(v___f_3988_, 4, v_inst_3980_);
lean_closure_set(v___f_3988_, 5, v_toBind_3981_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3986_);
lean_ctor_set(v___x_3989_, 1, v_val_3985_);
v_sz_3990_ = lean_array_size(v_params_3982_);
v___x_3991_ = ((size_t)0ULL);
v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3983_, v_params_3982_, v___f_3988_, v_sz_3990_, v___x_3991_, v___x_3989_);
v___x_3993_ = lean_apply_4(v_toBind_3981_, lean_box(0), lean_box(0), v___x_3992_, v___f_3984_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v_toPure_3994_, lean_object* v_levels_x3f_3995_, lean_object* v___x_3996_, lean_object* v_inst_3997_, lean_object* v_toBind_3998_, lean_object* v_params_3999_, lean_object* v_inst_4000_, lean_object* v___f_4001_, lean_object* v_val_4002_){
_start:
{
uint8_t v___x_950__boxed_4003_; lean_object* v_res_4004_; 
v___x_950__boxed_4003_ = lean_unbox(v___x_3996_);
v_res_4004_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v_toPure_3994_, v_levels_x3f_3995_, v___x_950__boxed_4003_, v_inst_3997_, v_toBind_3998_, v_params_3999_, v_inst_4000_, v___f_4001_, v_val_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4005_, lean_object* v_us_4006_, uint8_t v___x_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4005_, v_us_4006_, v___x_4007_, v___y_4010_, v___y_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4014_, lean_object* v_us_4015_, lean_object* v___x_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
uint8_t v___x_976__boxed_4022_; lean_object* v_res_4023_; 
v___x_976__boxed_4022_ = lean_unbox(v___x_4016_);
v_res_4023_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4014_, v_us_4015_, v___x_976__boxed_4022_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec_ref(v_cinfo_4014_);
return v_res_4023_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4027_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4028_ = lean_unsigned_to_nat(2u);
v___x_4029_ = lean_unsigned_to_nat(202u);
v___x_4030_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4031_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4032_ = l_mkPanicMessageWithDecl(v___x_4031_, v___x_4030_, v___x_4029_, v___x_4028_, v___x_4027_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4033_, lean_object* v_inst_4034_, lean_object* v_toPure_4035_, lean_object* v_levels_x3f_4036_, lean_object* v_inst_4037_, lean_object* v_toBind_4038_, lean_object* v_params_4039_, lean_object* v___f_4040_, lean_object* v_us_4041_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v___x_4042_ = l_List_lengthTR___redArg(v_us_4041_);
v___x_4043_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4033_);
v___x_4044_ = l_List_lengthTR___redArg(v___x_4043_);
lean_dec(v___x_4043_);
v___x_4045_ = lean_nat_dec_eq(v___x_4042_, v___x_4044_);
lean_dec(v___x_4044_);
lean_dec(v___x_4042_);
if (v___x_4045_ == 0)
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec(v_us_4041_);
lean_dec(v___f_4040_);
lean_dec_ref(v_params_4039_);
lean_dec(v_toBind_4038_);
lean_dec(v_inst_4037_);
lean_dec(v_levels_x3f_4036_);
lean_dec(v_toPure_4035_);
lean_dec_ref(v_cinfo_4033_);
v___x_4046_ = lean_box(0);
v___x_4047_ = l_instInhabitedOfMonad___redArg(v_inst_4034_, v___x_4046_);
v___x_4048_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4049_ = l_panic___redArg(v___x_4047_, v___x_4048_);
lean_dec(v___x_4047_);
return v___x_4049_;
}
else
{
lean_object* v___x_4050_; lean_object* v___f_4051_; uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4050_ = lean_box(v___x_4045_);
lean_inc(v_toBind_4038_);
lean_inc(v_inst_4037_);
v___f_4051_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_4051_, 0, v_toPure_4035_);
lean_closure_set(v___f_4051_, 1, v_levels_x3f_4036_);
lean_closure_set(v___f_4051_, 2, v___x_4050_);
lean_closure_set(v___f_4051_, 3, v_inst_4037_);
lean_closure_set(v___f_4051_, 4, v_toBind_4038_);
lean_closure_set(v___f_4051_, 5, v_params_4039_);
lean_closure_set(v___f_4051_, 6, v_inst_4034_);
lean_closure_set(v___f_4051_, 7, v___f_4040_);
v___x_4052_ = 0;
v___x_4053_ = lean_box(v___x_4052_);
v___f_4054_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4054_, 0, v_cinfo_4033_);
lean_closure_set(v___f_4054_, 1, v_us_4041_);
lean_closure_set(v___f_4054_, 2, v___x_4053_);
v___x_4055_ = lean_apply_2(v_inst_4037_, lean_box(0), v___f_4054_);
v___x_4056_ = lean_apply_4(v_toBind_4038_, lean_box(0), lean_box(0), v___x_4055_, v___f_4051_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4057_, lean_object* v_toPure_4058_, lean_object* v_levels_x3f_4059_, lean_object* v_inst_4060_, lean_object* v_toBind_4061_, lean_object* v_params_4062_, lean_object* v___f_4063_, lean_object* v_cinfo_4064_){
_start:
{
lean_object* v___f_4065_; 
lean_inc(v_toBind_4061_);
lean_inc(v_inst_4060_);
lean_inc(v_levels_x3f_4059_);
lean_inc(v_toPure_4058_);
lean_inc_ref(v_cinfo_4064_);
v___f_4065_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4065_, 0, v_cinfo_4064_);
lean_closure_set(v___f_4065_, 1, v_inst_4057_);
lean_closure_set(v___f_4065_, 2, v_toPure_4058_);
lean_closure_set(v___f_4065_, 3, v_levels_x3f_4059_);
lean_closure_set(v___f_4065_, 4, v_inst_4060_);
lean_closure_set(v___f_4065_, 5, v_toBind_4061_);
lean_closure_set(v___f_4065_, 6, v_params_4062_);
lean_closure_set(v___f_4065_, 7, v___f_4063_);
if (lean_obj_tag(v_levels_x3f_4059_) == 0)
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec(v_toPure_4058_);
v___x_4066_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4066_, 0, v_cinfo_4064_);
v___x_4067_ = lean_apply_2(v_inst_4060_, lean_box(0), v___x_4066_);
v___x_4068_ = lean_apply_4(v_toBind_4061_, lean_box(0), lean_box(0), v___x_4067_, v___f_4065_);
return v___x_4068_;
}
else
{
lean_object* v_val_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref(v_cinfo_4064_);
lean_dec(v_inst_4060_);
v_val_4069_ = lean_ctor_get(v_levels_x3f_4059_, 0);
lean_inc(v_val_4069_);
lean_dec_ref_known(v_levels_x3f_4059_, 1);
v___x_4070_ = lean_apply_2(v_toPure_4058_, lean_box(0), v_val_4069_);
v___x_4071_ = lean_apply_4(v_toBind_4061_, lean_box(0), lean_box(0), v___x_4070_, v___f_4065_);
return v___x_4071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4072_, lean_object* v_inst_4073_, lean_object* v_inst_4074_, lean_object* v_inst_4075_, lean_object* v_defaultFn_4076_, lean_object* v_levels_x3f_4077_, lean_object* v_params_4078_, lean_object* v_fieldVal_x3f_4079_){
_start:
{
lean_object* v_toApplicative_4080_; lean_object* v_toBind_4081_; lean_object* v_toPure_4082_; lean_object* v___x_4083_; lean_object* v___f_4084_; lean_object* v___f_4085_; lean_object* v___x_4086_; 
v_toApplicative_4080_ = lean_ctor_get(v_inst_4072_, 0);
v_toBind_4081_ = lean_ctor_get(v_inst_4072_, 1);
lean_inc_n(v_toBind_4081_, 2);
v_toPure_4082_ = lean_ctor_get(v_toApplicative_4080_, 1);
lean_inc_n(v_toPure_4082_, 2);
lean_inc_ref_n(v_inst_4072_, 2);
v___x_4083_ = l_Lean_getConstInfo___redArg(v_inst_4072_, v_inst_4073_, v_inst_4074_, v_defaultFn_4076_);
lean_inc(v_inst_4075_);
v___f_4084_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4084_, 0, v_inst_4072_);
lean_closure_set(v___f_4084_, 1, v_inst_4075_);
lean_closure_set(v___f_4084_, 2, v_fieldVal_x3f_4079_);
lean_closure_set(v___f_4084_, 3, v_toPure_4082_);
v___f_4085_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4085_, 0, v_inst_4072_);
lean_closure_set(v___f_4085_, 1, v_toPure_4082_);
lean_closure_set(v___f_4085_, 2, v_levels_x3f_4077_);
lean_closure_set(v___f_4085_, 3, v_inst_4075_);
lean_closure_set(v___f_4085_, 4, v_toBind_4081_);
lean_closure_set(v___f_4085_, 5, v_params_4078_);
lean_closure_set(v___f_4085_, 6, v___f_4084_);
v___x_4086_ = lean_apply_4(v_toBind_4081_, lean_box(0), lean_box(0), v___x_4083_, v___f_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4087_, lean_object* v_inst_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_inst_4091_, lean_object* v_inst_4092_, lean_object* v_defaultFn_4093_, lean_object* v_levels_x3f_4094_, lean_object* v_params_4095_, lean_object* v_fieldVal_x3f_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4088_, v_inst_4089_, v_inst_4090_, v_inst_4091_, v_defaultFn_4093_, v_levels_x3f_4094_, v_params_4095_, v_fieldVal_x3f_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4098_, lean_object* v_inst_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_defaultFn_4104_, lean_object* v_levels_x3f_4105_, lean_object* v_params_4106_, lean_object* v_fieldVal_x3f_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4098_, v_inst_4099_, v_inst_4100_, v_inst_4101_, v_inst_4102_, v_inst_4103_, v_defaultFn_4104_, v_levels_x3f_4105_, v_params_4106_, v_fieldVal_x3f_4107_);
lean_dec_ref(v_inst_4103_);
return v_res_4108_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Structure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
