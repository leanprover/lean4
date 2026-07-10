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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_18442__boxed_466_; lean_object* v_res_467_; 
v___x_18442__boxed_466_ = lean_unbox(v___x_456_);
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_18442__boxed_466_, v_projName_457_, v_n_458_, v_ref_459_, v___f_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
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
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_List_lengthTR___redArg(v_paramInfoOverrides_562_);
v___x_739_ = lean_array_get_size(v_params_556_);
v___x_740_ = lean_nat_dec_le(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_551_);
v___x_742_ = l_Lean_MessageData_ofName(v_projName_551_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v_n_563_);
v___x_746_ = l_Lean_MessageData_ofConstName(v_n_563_, v___x_740_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_564_, v___x_749_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref_known(v___x_750_, 1);
goto v___jp_698_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
goto v___jp_698_;
}
v___jp_573_:
{
lean_object* v___x_576_; lean_object* v_env_577_; lean_object* v_nextMacroScope_578_; lean_object* v_ngen_579_; lean_object* v_auxDeclNGen_580_; lean_object* v_traceState_581_; lean_object* v_messages_582_; lean_object* v_infoState_583_; lean_object* v_snapshotTasks_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_616_; 
v___x_576_ = lean_st_ref_take(v___y_575_);
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
v___x_593_ = lean_st_ref_set(v___y_575_, v___x_592_);
v___x_594_ = lean_st_ref_take(v___y_574_);
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
v___x_605_ = lean_st_ref_set(v___y_574_, v___x_604_);
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
lean_ctor_set(v___x_639_, 1, v___y_633_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*3, v___x_559_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = l_Lean_addDecl(v___x_640_, v___y_632_, v___y_634_, v___y_635_);
lean_dec_ref(v___y_634_);
v___y_619_ = v___y_631_;
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
uint8_t v___x_678_; 
lean_dec_ref_known(v___x_677_, 1);
v___x_678_ = lean_bool_not(v_instImplicit_554_);
if (v___x_678_ == 0)
{
lean_dec_ref_known(v___x_672_, 14);
v___y_574_ = v___y_646_;
v___y_575_ = v___y_648_;
goto v___jp_573_;
}
else
{
lean_object* v___x_679_; 
lean_inc(v_projName_551_);
v___x_679_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_551_, v___y_645_, v___y_646_, v___x_672_, v___y_648_);
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_646_;
v___y_620_ = v___y_648_;
v___y_621_ = v___x_679_;
goto v___jp_618_;
}
}
else
{
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_646_;
v___y_620_ = v___y_648_;
v___y_621_ = v___x_677_;
goto v___jp_618_;
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref_known(v___x_672_, 14);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_680_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_674_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_688_ = lean_st_ref_get(v___y_648_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref_n(v_env_689_, 2);
lean_dec(v___x_688_);
lean_inc_ref(v___x_668_);
lean_inc(v_projName_551_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v_projName_551_);
lean_ctor_set(v___x_690_, 1, v___x_565_);
lean_ctor_set(v___x_690_, 2, v___x_668_);
v___x_691_ = l_Lean_Environment_hasUnsafe(v_env_689_, v___x_668_);
lean_dec_ref(v___x_668_);
if (v___x_691_ == 0)
{
uint8_t v___x_692_; 
v___x_692_ = l_Lean_Environment_hasUnsafe(v_env_689_, v___x_670_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_693_ = lean_box(0);
lean_inc(v_projName_551_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v_projName_551_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_695_, 0, v___x_690_);
lean_ctor_set(v___x_695_, 1, v___x_670_);
lean_ctor_set(v___x_695_, 2, v___x_694_);
v___x_696_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
v___x_697_ = l_Lean_addDecl(v___x_696_, v___x_649_, v___x_672_, v___y_648_);
lean_dec_ref_known(v___x_672_, 14);
v___y_619_ = v___y_646_;
v___y_620_ = v___y_648_;
v___y_621_ = v___x_697_;
goto v___jp_618_;
}
else
{
v___y_631_ = v___y_646_;
v___y_632_ = v___x_649_;
v___y_633_ = v___x_670_;
v___y_634_ = v___x_672_;
v___y_635_ = v___y_648_;
v___y_636_ = v___x_690_;
goto v___jp_630_;
}
}
else
{
lean_dec_ref(v_env_689_);
v___y_631_ = v___y_646_;
v___y_632_ = v___x_649_;
v___y_633_ = v___x_670_;
v___y_634_ = v___x_672_;
v___y_635_ = v___y_648_;
v___y_636_ = v___x_690_;
goto v___jp_630_;
}
}
}
v___jp_698_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = l_Lean_Expr_bindingDomain_x21(v_b_558_);
v___x_700_ = lean_expr_consume_type_annotations(v___x_699_);
lean_inc_ref(v___x_700_);
v___x_701_ = l_Lean_Meta_isProp(v___x_700_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_701_) == 0)
{
if (v_a_566_ == 0)
{
lean_object* v_a_702_; uint8_t v___x_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_unbox(v_a_702_);
lean_dec(v_a_702_);
v___y_643_ = v___x_703_;
v___y_644_ = v___x_700_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
else
{
lean_object* v_a_704_; uint8_t v___x_705_; uint8_t v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_701_, 1);
v___x_705_ = lean_unbox(v_a_704_);
v___x_706_ = lean_bool_not(v___x_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
v___x_707_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
v___y_643_ = v___x_707_;
v___y_644_ = v___x_700_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_708_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_551_);
v___x_709_ = l_Lean_MessageData_ofName(v_projName_551_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = 0;
lean_inc(v_n_563_);
v___x_714_ = l_Lean_MessageData_ofConstName(v_n_563_, v___x_713_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_inc_ref(v___x_700_);
v___x_718_ = l_Lean_indentExpr(v___x_700_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_564_, v___x_719_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_720_) == 0)
{
uint8_t v___x_721_; 
lean_dec_ref_known(v___x_720_, 1);
v___x_721_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
v___y_643_ = v___x_721_;
v___y_644_ = v___x_700_;
v___y_645_ = v___y_568_;
v___y_646_ = v___y_569_;
v___y_647_ = v___y_570_;
v___y_648_ = v___y_571_;
goto v___jp_642_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_704_);
lean_dec_ref(v___x_700_);
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_722_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_700_);
lean_dec(v___x_565_);
lean_dec(v_n_563_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_self_557_);
lean_dec(v___x_555_);
lean_dec(v_a_553_);
lean_dec(v___x_552_);
lean_dec(v_projName_551_);
lean_dec_ref(v___x_550_);
v_a_730_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_701_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_701_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_759_ = _args[0];
lean_object* v_projName_760_ = _args[1];
lean_object* v___x_761_ = _args[2];
lean_object* v_a_762_ = _args[3];
lean_object* v_instImplicit_763_ = _args[4];
lean_object* v___x_764_ = _args[5];
lean_object* v_params_765_ = _args[6];
lean_object* v_self_766_ = _args[7];
lean_object* v_b_767_ = _args[8];
lean_object* v___x_768_ = _args[9];
lean_object* v_a_769_ = _args[10];
lean_object* v___x_770_ = _args[11];
lean_object* v_paramInfoOverrides_771_ = _args[12];
lean_object* v_n_772_ = _args[13];
lean_object* v_ref_773_ = _args[14];
lean_object* v___x_774_ = _args[15];
lean_object* v_a_775_ = _args[16];
lean_object* v_____r_776_ = _args[17];
lean_object* v___y_777_ = _args[18];
lean_object* v___y_778_ = _args[19];
lean_object* v___y_779_ = _args[20];
lean_object* v___y_780_ = _args[21];
lean_object* v___y_781_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_782_; uint8_t v___x_18681__boxed_783_; uint8_t v_a_18687__boxed_784_; lean_object* v_res_785_; 
v_instImplicit_boxed_782_ = lean_unbox(v_instImplicit_763_);
v___x_18681__boxed_783_ = lean_unbox(v___x_768_);
v_a_18687__boxed_784_ = lean_unbox(v_a_775_);
v_res_785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_759_, v_projName_760_, v___x_761_, v_a_762_, v_instImplicit_boxed_782_, v___x_764_, v_params_765_, v_self_766_, v_b_767_, v___x_18681__boxed_783_, v_a_769_, v___x_770_, v_paramInfoOverrides_771_, v_n_772_, v_ref_773_, v___x_774_, v_a_18687__boxed_784_, v_____r_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v_ref_773_);
lean_dec(v_paramInfoOverrides_771_);
lean_dec_ref(v___x_770_);
lean_dec_ref(v_b_767_);
lean_dec_ref(v_params_765_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_786_, uint8_t v_isExporting_787_, lean_object* v___x_788_, lean_object* v___y_789_, lean_object* v___x_790_, lean_object* v_a_x3f_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_env_794_; lean_object* v_nextMacroScope_795_; lean_object* v_ngen_796_; lean_object* v_auxDeclNGen_797_; lean_object* v_traceState_798_; lean_object* v_messages_799_; lean_object* v_infoState_800_; lean_object* v_snapshotTasks_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_826_; 
v___x_793_ = lean_st_ref_take(v___y_786_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
v_nextMacroScope_795_ = lean_ctor_get(v___x_793_, 1);
v_ngen_796_ = lean_ctor_get(v___x_793_, 2);
v_auxDeclNGen_797_ = lean_ctor_get(v___x_793_, 3);
v_traceState_798_ = lean_ctor_get(v___x_793_, 4);
v_messages_799_ = lean_ctor_get(v___x_793_, 6);
v_infoState_800_ = lean_ctor_get(v___x_793_, 7);
v_snapshotTasks_801_ = lean_ctor_get(v___x_793_, 8);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_793_, 5);
lean_dec(v_unused_827_);
v___x_803_ = v___x_793_;
v_isShared_804_ = v_isSharedCheck_826_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snapshotTasks_801_);
lean_inc(v_infoState_800_);
lean_inc(v_messages_799_);
lean_inc(v_traceState_798_);
lean_inc(v_auxDeclNGen_797_);
lean_inc(v_ngen_796_);
lean_inc(v_nextMacroScope_795_);
lean_inc(v_env_794_);
lean_dec(v___x_793_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_826_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_Environment_setExporting(v_env_794_, v_isExporting_787_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 5, v___x_788_);
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_nextMacroScope_795_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_ngen_796_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_auxDeclNGen_797_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_traceState_798_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_825_, 6, v_messages_799_);
lean_ctor_set(v_reuseFailAlloc_825_, 7, v_infoState_800_);
lean_ctor_set(v_reuseFailAlloc_825_, 8, v_snapshotTasks_801_);
v___x_807_ = v_reuseFailAlloc_825_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_mctx_810_; lean_object* v_zetaDeltaFVarIds_811_; lean_object* v_postponed_812_; lean_object* v_diag_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_823_; 
v___x_808_ = lean_st_ref_set(v___y_786_, v___x_807_);
v___x_809_ = lean_st_ref_take(v___y_789_);
v_mctx_810_ = lean_ctor_get(v___x_809_, 0);
v_zetaDeltaFVarIds_811_ = lean_ctor_get(v___x_809_, 2);
v_postponed_812_ = lean_ctor_get(v___x_809_, 3);
v_diag_813_ = lean_ctor_get(v___x_809_, 4);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v___x_809_, 1);
lean_dec(v_unused_824_);
v___x_815_ = v___x_809_;
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_diag_813_);
lean_inc(v_postponed_812_);
lean_inc(v_zetaDeltaFVarIds_811_);
lean_inc(v_mctx_810_);
lean_dec(v___x_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_823_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v___x_790_);
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_mctx_810_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_zetaDeltaFVarIds_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_postponed_812_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_diag_813_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_st_ref_set(v___y_789_, v___x_818_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_828_, lean_object* v_isExporting_829_, lean_object* v___x_830_, lean_object* v___y_831_, lean_object* v___x_832_, lean_object* v_a_x3f_833_, lean_object* v___y_834_){
_start:
{
uint8_t v_isExporting_boxed_835_; lean_object* v_res_836_; 
v_isExporting_boxed_835_ = lean_unbox(v_isExporting_829_);
v_res_836_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_828_, v_isExporting_boxed_835_, v___x_830_, v___y_831_, v___x_832_, v_a_x3f_833_);
lean_dec(v_a_x3f_833_);
lean_dec(v___y_831_);
lean_dec(v___y_828_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_837_, uint8_t v_isExporting_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_env_845_; uint8_t v_isExporting_846_; uint8_t v___y_913_; lean_object* v___x_915_; uint8_t v_isModule_916_; uint8_t v___x_917_; 
v___x_844_ = lean_st_ref_get(v___y_842_);
v_env_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_env_845_);
lean_dec(v___x_844_);
v_isExporting_846_ = lean_ctor_get_uint8(v_env_845_, sizeof(void*)*8);
v___x_915_ = l_Lean_Environment_header(v_env_845_);
lean_dec_ref(v_env_845_);
v_isModule_916_ = lean_ctor_get_uint8(v___x_915_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_915_);
v___x_917_ = lean_bool_not(v_isModule_916_);
if (v___x_917_ == 0)
{
if (v_isExporting_846_ == 0)
{
if (v_isExporting_838_ == 0)
{
lean_object* v___x_918_; 
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
v___x_918_ = lean_apply_5(v_x_837_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
return v___x_918_;
}
else
{
goto v___jp_847_;
}
}
else
{
v___y_913_ = v_isExporting_838_;
goto v___jp_912_;
}
}
else
{
v___y_913_ = v___x_917_;
goto v___jp_912_;
}
v___jp_847_:
{
lean_object* v___x_848_; lean_object* v_env_849_; lean_object* v_nextMacroScope_850_; lean_object* v_ngen_851_; lean_object* v_auxDeclNGen_852_; lean_object* v_traceState_853_; lean_object* v_messages_854_; lean_object* v_infoState_855_; lean_object* v_snapshotTasks_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_910_; 
v___x_848_ = lean_st_ref_take(v___y_842_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
v_nextMacroScope_850_ = lean_ctor_get(v___x_848_, 1);
v_ngen_851_ = lean_ctor_get(v___x_848_, 2);
v_auxDeclNGen_852_ = lean_ctor_get(v___x_848_, 3);
v_traceState_853_ = lean_ctor_get(v___x_848_, 4);
v_messages_854_ = lean_ctor_get(v___x_848_, 6);
v_infoState_855_ = lean_ctor_get(v___x_848_, 7);
v_snapshotTasks_856_ = lean_ctor_get(v___x_848_, 8);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_848_, 5);
lean_dec(v_unused_911_);
v___x_858_ = v___x_848_;
v_isShared_859_ = v_isSharedCheck_910_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snapshotTasks_856_);
lean_inc(v_infoState_855_);
lean_inc(v_messages_854_);
lean_inc(v_traceState_853_);
lean_inc(v_auxDeclNGen_852_);
lean_inc(v_ngen_851_);
lean_inc(v_nextMacroScope_850_);
lean_inc(v_env_849_);
lean_dec(v___x_848_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_910_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = l_Lean_Environment_setExporting(v_env_849_, v_isExporting_838_);
v___x_861_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 5, v___x_861_);
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_nextMacroScope_850_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_ngen_851_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_auxDeclNGen_852_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_traceState_853_);
lean_ctor_set(v_reuseFailAlloc_909_, 5, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_909_, 6, v_messages_854_);
lean_ctor_set(v_reuseFailAlloc_909_, 7, v_infoState_855_);
lean_ctor_set(v_reuseFailAlloc_909_, 8, v_snapshotTasks_856_);
v___x_863_ = v_reuseFailAlloc_909_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_mctx_866_; lean_object* v_zetaDeltaFVarIds_867_; lean_object* v_postponed_868_; lean_object* v_diag_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_907_; 
v___x_864_ = lean_st_ref_set(v___y_842_, v___x_863_);
v___x_865_ = lean_st_ref_take(v___y_840_);
v_mctx_866_ = lean_ctor_get(v___x_865_, 0);
v_zetaDeltaFVarIds_867_ = lean_ctor_get(v___x_865_, 2);
v_postponed_868_ = lean_ctor_get(v___x_865_, 3);
v_diag_869_ = lean_ctor_get(v___x_865_, 4);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_865_, 1);
lean_dec(v_unused_908_);
v___x_871_ = v___x_865_;
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_diag_869_);
lean_inc(v_postponed_868_);
lean_inc(v_zetaDeltaFVarIds_867_);
lean_inc(v_mctx_866_);
lean_dec(v___x_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_907_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_mctx_866_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_zetaDeltaFVarIds_867_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_postponed_868_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_diag_869_);
v___x_875_ = v_reuseFailAlloc_906_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v_r_877_; 
v___x_876_ = lean_st_ref_set(v___y_840_, v___x_875_);
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
v_r_877_ = lean_apply_5(v_x_837_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
if (lean_obj_tag(v_r_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_894_; 
v_a_878_ = lean_ctor_get(v_r_877_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_r_877_);
if (v_isSharedCheck_894_ == 0)
{
v___x_880_ = v_r_877_;
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v_r_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_894_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
lean_inc(v_a_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 1);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v___x_884_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_842_, v_isExporting_846_, v___x_861_, v___y_840_, v___x_873_, v___x_883_);
lean_dec_ref(v___x_883_);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v___x_884_, 0);
lean_dec(v_unused_892_);
v___x_886_ = v___x_884_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_dec(v___x_884_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_a_878_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_878_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_895_ = lean_ctor_get(v_r_877_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v_r_877_, 1);
v___x_896_ = lean_box(0);
v___x_897_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_842_, v_isExporting_846_, v___x_861_, v___y_840_, v___x_873_, v___x_896_);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_905_);
v___x_899_ = v___x_897_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_897_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 1);
lean_ctor_set(v___x_899_, 0, v_a_895_);
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_895_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
}
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
goto v___jp_847_;
}
else
{
lean_object* v___x_914_; 
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
v___x_914_ = lean_apply_5(v_x_837_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, lean_box(0));
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_919_, lean_object* v_isExporting_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_isExporting_boxed_926_; lean_object* v_res_927_; 
v_isExporting_boxed_926_ = lean_unbox(v_isExporting_920_);
v_res_927_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_919_, v_isExporting_boxed_926_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_928_, uint8_t v_when_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
if (v_when_929_ == 0)
{
lean_object* v___x_935_; 
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
v___x_935_ = lean_apply_5(v_x_928_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, lean_box(0));
return v___x_935_;
}
else
{
uint8_t v___x_936_; lean_object* v___x_937_; 
v___x_936_ = 0;
v___x_937_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_928_, v___x_936_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_938_, lean_object* v_when_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
uint8_t v_when_boxed_945_; lean_object* v_res_946_; 
v_when_boxed_945_ = lean_unbox(v_when_939_);
v_res_946_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_938_, v_when_boxed_945_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_947_, lean_object* v_projDecls_948_, lean_object* v___x_949_, lean_object* v___x_950_, uint8_t v_instImplicit_951_, lean_object* v___x_952_, lean_object* v_params_953_, lean_object* v_self_954_, lean_object* v_a_955_, lean_object* v___x_956_, lean_object* v_n_957_, lean_object* v___x_958_, uint8_t v_a_959_, lean_object* v_a_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_lt(v_a_960_, v_upperBound_947_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; 
lean_dec(v_a_960_);
lean_dec(v___x_958_);
lean_dec(v_n_957_);
lean_dec_ref(v___x_956_);
lean_dec_ref(v_a_955_);
lean_dec_ref(v_self_954_);
lean_dec_ref(v_params_953_);
lean_dec(v___x_952_);
lean_dec(v___x_950_);
lean_dec_ref(v___x_949_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v_b_961_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v_ref_970_; lean_object* v_projName_971_; lean_object* v_paramInfoOverrides_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___f_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___y_979_; uint8_t v___x_980_; lean_object* v___x_981_; 
v___x_969_ = lean_array_fget_borrowed(v_projDecls_948_, v_a_960_);
v_ref_970_ = lean_ctor_get(v___x_969_, 0);
v_projName_971_ = lean_ctor_get(v___x_969_, 1);
v_paramInfoOverrides_972_ = lean_ctor_get(v___x_969_, 2);
v___x_973_ = lean_box(v_instImplicit_951_);
v___x_974_ = lean_box(v___x_967_);
v___x_975_ = lean_box(v_a_959_);
lean_inc(v___x_958_);
lean_inc_n(v_ref_970_, 2);
lean_inc_n(v_n_957_, 2);
lean_inc(v_paramInfoOverrides_972_);
lean_inc_ref(v___x_956_);
lean_inc_ref(v_a_955_);
lean_inc_ref(v_b_961_);
lean_inc_ref(v_self_954_);
lean_inc_ref(v_params_953_);
lean_inc(v___x_952_);
lean_inc(v_a_960_);
lean_inc(v___x_950_);
lean_inc_n(v_projName_971_, 2);
lean_inc_ref(v___x_949_);
v___f_976_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_976_, 0, v___x_949_);
lean_closure_set(v___f_976_, 1, v_projName_971_);
lean_closure_set(v___f_976_, 2, v___x_950_);
lean_closure_set(v___f_976_, 3, v_a_960_);
lean_closure_set(v___f_976_, 4, v___x_973_);
lean_closure_set(v___f_976_, 5, v___x_952_);
lean_closure_set(v___f_976_, 6, v_params_953_);
lean_closure_set(v___f_976_, 7, v_self_954_);
lean_closure_set(v___f_976_, 8, v_b_961_);
lean_closure_set(v___f_976_, 9, v___x_974_);
lean_closure_set(v___f_976_, 10, v_a_955_);
lean_closure_set(v___f_976_, 11, v___x_956_);
lean_closure_set(v___f_976_, 12, v_paramInfoOverrides_972_);
lean_closure_set(v___f_976_, 13, v_n_957_);
lean_closure_set(v___f_976_, 14, v_ref_970_);
lean_closure_set(v___f_976_, 15, v___x_958_);
lean_closure_set(v___f_976_, 16, v___x_975_);
v___x_977_ = l_Lean_Expr_isForall(v_b_961_);
lean_dec_ref(v_b_961_);
v___x_978_ = lean_box(v___x_977_);
v___y_979_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_979_, 0, v___x_978_);
lean_closure_set(v___y_979_, 1, v_projName_971_);
lean_closure_set(v___y_979_, 2, v_n_957_);
lean_closure_set(v___y_979_, 3, v_ref_970_);
lean_closure_set(v___y_979_, 4, v___f_976_);
v___x_980_ = l_Lean_isPrivateName(v_projName_971_);
v___x_981_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_979_, v___x_980_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_add(v_a_960_, v___x_983_);
lean_dec(v_a_960_);
v_a_960_ = v___x_984_;
v_b_961_ = v_a_982_;
goto _start;
}
else
{
lean_dec(v_a_960_);
lean_dec(v___x_958_);
lean_dec(v_n_957_);
lean_dec_ref(v___x_956_);
lean_dec_ref(v_a_955_);
lean_dec_ref(v_self_954_);
lean_dec_ref(v_params_953_);
lean_dec(v___x_952_);
lean_dec(v___x_950_);
lean_dec_ref(v___x_949_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_986_ = _args[0];
lean_object* v_projDecls_987_ = _args[1];
lean_object* v___x_988_ = _args[2];
lean_object* v___x_989_ = _args[3];
lean_object* v_instImplicit_990_ = _args[4];
lean_object* v___x_991_ = _args[5];
lean_object* v_params_992_ = _args[6];
lean_object* v_self_993_ = _args[7];
lean_object* v_a_994_ = _args[8];
lean_object* v___x_995_ = _args[9];
lean_object* v_n_996_ = _args[10];
lean_object* v___x_997_ = _args[11];
lean_object* v_a_998_ = _args[12];
lean_object* v_a_999_ = _args[13];
lean_object* v_b_1000_ = _args[14];
lean_object* v___y_1001_ = _args[15];
lean_object* v___y_1002_ = _args[16];
lean_object* v___y_1003_ = _args[17];
lean_object* v___y_1004_ = _args[18];
lean_object* v___y_1005_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1006_; uint8_t v_a_19293__boxed_1007_; lean_object* v_res_1008_; 
v_instImplicit_boxed_1006_ = lean_unbox(v_instImplicit_990_);
v_a_19293__boxed_1007_ = lean_unbox(v_a_998_);
v_res_1008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_986_, v_projDecls_987_, v___x_988_, v___x_989_, v_instImplicit_boxed_1006_, v___x_991_, v_params_992_, v_self_993_, v_a_994_, v___x_995_, v_n_996_, v___x_997_, v_a_19293__boxed_1007_, v_a_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_projDecls_987_);
lean_dec(v_upperBound_986_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1009_, lean_object* v_as_1010_, size_t v_sz_1011_, size_t v_i_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_usize_dec_lt(v_i_1012_, v_sz_1011_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_b_1013_);
return v___x_1019_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_array_uget_borrowed(v_as_1010_, v_i_1012_);
v___x_1021_ = l_Lean_Expr_fvarId_x21(v_a_1020_);
lean_inc(v___x_1021_);
v___x_1022_ = l_Lean_FVarId_getDecl___redArg(v___x_1021_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v_a_1025_; uint8_t v___y_1030_; uint8_t v___x_1033_; uint8_t v___x_1034_; uint8_t v___y_1036_; uint8_t v___x_1039_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1033_ = l_Lean_LocalDecl_binderInfo(v_a_1023_);
v___x_1034_ = l_Lean_BinderInfo_isInstImplicit(v___x_1033_);
v___x_1039_ = lean_bool_not(v___x_1034_);
if (v___x_1039_ == 0)
{
lean_dec(v_a_1023_);
v___y_1036_ = v___x_1039_;
goto v___jp_1035_;
}
else
{
lean_object* v___x_1040_; uint8_t v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = l_Lean_LocalDecl_type(v_a_1023_);
lean_dec(v_a_1023_);
v___x_1041_ = l_Lean_Expr_isOutParam(v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = lean_bool_not(v___x_1041_);
v___y_1036_ = v___x_1042_;
goto v___jp_1035_;
}
v___jp_1024_:
{
size_t v___x_1026_; size_t v___x_1027_; 
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1012_, v___x_1026_);
v_i_1012_ = v___x_1027_;
v_b_1013_ = v_a_1025_;
goto _start;
}
v___jp_1029_:
{
if (v___y_1030_ == 0)
{
lean_dec(v___x_1021_);
v_a_1025_ = v_b_1013_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 1;
v___x_1032_ = l_Lean_LocalContext_setBinderInfo(v_b_1013_, v___x_1021_, v___x_1031_);
v_a_1025_ = v___x_1032_;
goto v___jp_1024_;
}
}
v___jp_1035_:
{
if (v___y_1036_ == 0)
{
if (v___x_1034_ == 0)
{
v___y_1030_ = v___x_1034_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v_instImplicit_1009_;
goto v___jp_1029_;
}
}
else
{
uint8_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = 0;
v___x_1038_ = l_Lean_LocalContext_setBinderInfo(v_b_1013_, v___x_1021_, v___x_1037_);
v_a_1025_ = v___x_1038_;
goto v___jp_1024_;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v___x_1021_);
lean_dec_ref(v_b_1013_);
v_a_1043_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1022_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1022_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1051_, lean_object* v_as_1052_, lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v_instImplicit_boxed_1060_; size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_instImplicit_boxed_1060_ = lean_unbox(v_instImplicit_1051_);
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1060_, v_as_1052_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1064_, uint8_t v_instImplicit_1065_, lean_object* v_projDecls_1066_, lean_object* v_toConstantVal_1067_, lean_object* v_numParams_1068_, lean_object* v___x_1069_, lean_object* v_n_1070_, lean_object* v_levelParams_1071_, uint8_t v_a_1072_, lean_object* v_ctorType_1073_, lean_object* v_self_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_lctx_1080_; lean_object* v___x_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_lctx_1080_ = lean_ctor_get(v___y_1075_, 2);
lean_inc_ref(v_self_1074_);
lean_inc_ref(v_params_1064_);
v___x_1081_ = lean_array_push(v_params_1064_, v_self_1074_);
v_sz_1082_ = lean_array_size(v_params_1064_);
v___x_1083_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1080_);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1065_, v_params_1064_, v_sz_1082_, v___x_1083_, v_lctx_1080_, v___y_1075_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = lean_array_get_size(v_projDecls_1066_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1086_, v_projDecls_1066_, v_toConstantVal_1067_, v_numParams_1068_, v_instImplicit_1065_, v___x_1069_, v_params_1064_, v_self_1074_, v_a_1085_, v___x_1081_, v_n_1070_, v_levelParams_1071_, v_a_1072_, v___x_1087_, v_ctorType_1073_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1088_, 0);
lean_dec(v_unused_1097_);
v___x_1090_ = v___x_1088_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v___x_1088_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1088_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1088_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_self_1074_);
lean_dec_ref(v_ctorType_1073_);
lean_dec(v_levelParams_1071_);
lean_dec(v_n_1070_);
lean_dec(v___x_1069_);
lean_dec(v_numParams_1068_);
lean_dec_ref(v_toConstantVal_1067_);
lean_dec_ref(v_params_1064_);
v_a_1106_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1084_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1084_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1114_, lean_object* v_instImplicit_1115_, lean_object* v_projDecls_1116_, lean_object* v_toConstantVal_1117_, lean_object* v_numParams_1118_, lean_object* v___x_1119_, lean_object* v_n_1120_, lean_object* v_levelParams_1121_, lean_object* v_a_1122_, lean_object* v_ctorType_1123_, lean_object* v_self_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_instImplicit_boxed_1130_; uint8_t v_a_19441__boxed_1131_; lean_object* v_res_1132_; 
v_instImplicit_boxed_1130_ = lean_unbox(v_instImplicit_1115_);
v_a_19441__boxed_1131_ = lean_unbox(v_a_1122_);
v_res_1132_ = l_Lean_Meta_mkProjections___lam__0(v_params_1114_, v_instImplicit_boxed_1130_, v_projDecls_1116_, v_toConstantVal_1117_, v_numParams_1118_, v___x_1119_, v_n_1120_, v_levelParams_1121_, v_a_19441__boxed_1131_, v_ctorType_1123_, v_self_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v_projDecls_1116_);
return v_res_1132_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1142_, lean_object* v_projDecls_1143_, lean_object* v_toConstantVal_1144_, lean_object* v_numParams_1145_, lean_object* v___x_1146_, lean_object* v_n_1147_, lean_object* v_levelParams_1148_, uint8_t v_a_1149_, lean_object* v_params_1150_, lean_object* v_ctorType_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; uint8_t v___y_1164_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1168_ = lean_box(v_instImplicit_1142_);
v___x_1169_ = lean_box(v_a_1149_);
lean_inc(v_n_1147_);
lean_inc(v___x_1146_);
lean_inc(v_numParams_1145_);
lean_inc_ref(v_params_1150_);
v___f_1170_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1170_, 0, v_params_1150_);
lean_closure_set(v___f_1170_, 1, v___x_1168_);
lean_closure_set(v___f_1170_, 2, v_projDecls_1143_);
lean_closure_set(v___f_1170_, 3, v_toConstantVal_1144_);
lean_closure_set(v___f_1170_, 4, v_numParams_1145_);
lean_closure_set(v___f_1170_, 5, v___x_1146_);
lean_closure_set(v___f_1170_, 6, v_n_1147_);
lean_closure_set(v___f_1170_, 7, v_levelParams_1148_);
lean_closure_set(v___f_1170_, 8, v___x_1169_);
lean_closure_set(v___f_1170_, 9, v_ctorType_1151_);
v___x_1176_ = lean_array_get_size(v_params_1150_);
v___x_1177_ = lean_nat_dec_eq(v___x_1176_, v_numParams_1145_);
lean_dec(v_numParams_1145_);
v___x_1178_ = lean_bool_not(v___x_1177_);
if (v___x_1178_ == 0)
{
goto v___jp_1171_;
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v___f_1170_);
lean_dec_ref(v_params_1150_);
lean_dec(v___x_1146_);
v___x_1179_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_MessageData_ofConstName(v_n_1147_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1179_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1184_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1185_;
}
v___jp_1157_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1166_ = 0;
v___x_1167_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1165_, v___y_1164_, v___y_1160_, v___y_1162_, v___x_1166_, v___y_1159_, v___y_1161_, v___y_1158_, v___y_1163_);
return v___x_1167_;
}
v___jp_1171_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = l_Lean_Expr_const___override(v_n_1147_, v___x_1146_);
v___x_1173_ = l_Lean_mkAppN(v___x_1172_, v_params_1150_);
lean_dec_ref(v_params_1150_);
if (v_instImplicit_1142_ == 0)
{
uint8_t v___x_1174_; 
v___x_1174_ = 0;
v___y_1158_ = v___y_1154_;
v___y_1159_ = v___y_1152_;
v___y_1160_ = v___x_1173_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___f_1170_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___x_1174_;
goto v___jp_1157_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = 3;
v___y_1158_ = v___y_1154_;
v___y_1159_ = v___y_1152_;
v___y_1160_ = v___x_1173_;
v___y_1161_ = v___y_1153_;
v___y_1162_ = v___f_1170_;
v___y_1163_ = v___y_1155_;
v___y_1164_ = v___x_1175_;
goto v___jp_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1186_, lean_object* v_projDecls_1187_, lean_object* v_toConstantVal_1188_, lean_object* v_numParams_1189_, lean_object* v___x_1190_, lean_object* v_n_1191_, lean_object* v_levelParams_1192_, lean_object* v_a_1193_, lean_object* v_params_1194_, lean_object* v_ctorType_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v_instImplicit_boxed_1201_; uint8_t v_a_19545__boxed_1202_; lean_object* v_res_1203_; 
v_instImplicit_boxed_1201_ = lean_unbox(v_instImplicit_1186_);
v_a_19545__boxed_1202_ = lean_unbox(v_a_1193_);
v_res_1203_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1201_, v_projDecls_1187_, v_toConstantVal_1188_, v_numParams_1189_, v___x_1190_, v_n_1191_, v_levelParams_1192_, v_a_19545__boxed_1202_, v_params_1194_, v_ctorType_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
if (lean_obj_tag(v_a_1204_) == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = l_List_reverse___redArg(v_a_1205_);
return v___x_1206_;
}
else
{
lean_object* v_head_1207_; lean_object* v_tail_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1217_; 
v_head_1207_ = lean_ctor_get(v_a_1204_, 0);
v_tail_1208_ = lean_ctor_get(v_a_1204_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1210_ = v_a_1204_;
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_tail_1208_);
lean_inc(v_head_1207_);
lean_dec(v_a_1204_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = l_Lean_mkLevelParam(v_head_1207_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v_a_1205_);
lean_ctor_set(v___x_1210_, 0, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_a_1205_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
v_a_1204_ = v_tail_1208_;
v_a_1205_ = v___x_1214_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_instMonadEIO(lean_box(0));
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_toApplicative_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1292_; 
v___x_1229_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1230_ = l_StateRefT_x27_instMonad___redArg(v___x_1229_);
v_toApplicative_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1230_, 1);
lean_dec(v_unused_1293_);
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1292_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_toApplicative_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1292_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_toFunctor_1235_; lean_object* v_toSeq_1236_; lean_object* v_toSeqLeft_1237_; lean_object* v_toSeqRight_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1290_; 
v_toFunctor_1235_ = lean_ctor_get(v_toApplicative_1231_, 0);
v_toSeq_1236_ = lean_ctor_get(v_toApplicative_1231_, 2);
v_toSeqLeft_1237_ = lean_ctor_get(v_toApplicative_1231_, 3);
v_toSeqRight_1238_ = lean_ctor_get(v_toApplicative_1231_, 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_toApplicative_1231_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v_toApplicative_1231_, 1);
lean_dec(v_unused_1291_);
v___x_1240_ = v_toApplicative_1231_;
v_isShared_1241_ = v_isSharedCheck_1290_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_toSeqRight_1238_);
lean_inc(v_toSeqLeft_1237_);
lean_inc(v_toSeq_1236_);
lean_inc(v_toFunctor_1235_);
lean_dec(v_toApplicative_1231_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1290_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1251_; 
v___f_1242_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1243_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1235_);
v___f_1244_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1244_, 0, v_toFunctor_1235_);
v___f_1245_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1245_, 0, v_toFunctor_1235_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___f_1244_);
lean_ctor_set(v___x_1246_, 1, v___f_1245_);
v___f_1247_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1247_, 0, v_toSeqRight_1238_);
v___f_1248_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1248_, 0, v_toSeqLeft_1237_);
v___f_1249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1249_, 0, v_toSeq_1236_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 4, v___f_1247_);
lean_ctor_set(v___x_1240_, 3, v___f_1248_);
lean_ctor_set(v___x_1240_, 2, v___f_1249_);
lean_ctor_set(v___x_1240_, 1, v___f_1242_);
lean_ctor_set(v___x_1240_, 0, v___x_1246_);
v___x_1251_ = v___x_1240_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v___f_1249_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v___f_1248_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v___f_1247_);
v___x_1251_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___f_1243_);
lean_ctor_set(v___x_1233_, 0, v___x_1251_);
v___x_1253_ = v___x_1233_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___f_1243_);
v___x_1253_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v_toApplicative_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1286_; 
v___x_1254_ = l_StateRefT_x27_instMonad___redArg(v___x_1253_);
v_toApplicative_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1254_, 1);
lean_dec(v_unused_1287_);
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1286_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_toApplicative_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1286_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_toFunctor_1259_; lean_object* v_toSeq_1260_; lean_object* v_toSeqLeft_1261_; lean_object* v_toSeqRight_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1284_; 
v_toFunctor_1259_ = lean_ctor_get(v_toApplicative_1255_, 0);
v_toSeq_1260_ = lean_ctor_get(v_toApplicative_1255_, 2);
v_toSeqLeft_1261_ = lean_ctor_get(v_toApplicative_1255_, 3);
v_toSeqRight_1262_ = lean_ctor_get(v_toApplicative_1255_, 4);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_toApplicative_1255_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v_toApplicative_1255_, 1);
lean_dec(v_unused_1285_);
v___x_1264_ = v_toApplicative_1255_;
v_isShared_1265_ = v_isSharedCheck_1284_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_toSeqRight_1262_);
lean_inc(v_toSeqLeft_1261_);
lean_inc(v_toSeq_1260_);
lean_inc(v_toFunctor_1259_);
lean_dec(v_toApplicative_1255_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1284_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___x_1275_; 
v___f_1266_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1267_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1259_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toFunctor_1259_);
v___f_1269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1269_, 0, v_toFunctor_1259_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___f_1268_);
lean_ctor_set(v___x_1270_, 1, v___f_1269_);
v___f_1271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1271_, 0, v_toSeqRight_1262_);
v___f_1272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1272_, 0, v_toSeqLeft_1261_);
v___f_1273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1273_, 0, v_toSeq_1260_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 4, v___f_1271_);
lean_ctor_set(v___x_1264_, 3, v___f_1272_);
lean_ctor_set(v___x_1264_, 2, v___f_1273_);
lean_ctor_set(v___x_1264_, 1, v___f_1266_);
lean_ctor_set(v___x_1264_, 0, v___x_1270_);
v___x_1275_ = v___x_1264_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___f_1266_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___f_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v___f_1272_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___f_1271_);
v___x_1275_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___f_1267_);
lean_ctor_set(v___x_1257_, 0, v___x_1275_);
v___x_1277_ = v___x_1257_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___f_1267_);
v___x_1277_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_14342__overap_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = l_instInhabitedOfMonad___redArg(v___x_1277_, v___x_1278_);
v___x_14342__overap_1280_ = lean_panic_fn_borrowed(v___x_1279_, v_msg_1223_);
lean_dec(v___x_1279_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1281_ = lean_apply_5(v___x_14342__overap_1280_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
return v___x_1281_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1307_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1308_ = lean_unsigned_to_nat(11u);
v___x_1309_ = lean_unsigned_to_nat(122u);
v___x_1310_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1311_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1312_ = l_mkPanicMessageWithDecl(v___x_1311_, v___x_1310_, v___x_1309_, v___x_1308_, v___x_1307_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1327_; lean_object* v_env_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_st_ref_get(v___y_1317_);
v_env_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_env_1328_);
lean_dec(v___x_1327_);
v___x_1329_ = 0;
lean_inc(v_constName_1313_);
v___x_1330_ = l_Lean_Environment_findAsync_x3f(v_env_1328_, v_constName_1313_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 1)
{
lean_object* v_val_1331_; uint8_t v_kind_1332_; 
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v_kind_1332_ = lean_ctor_get_uint8(v_val_1331_, sizeof(void*)*3);
if (v_kind_1332_ == 6)
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1331_);
if (lean_obj_tag(v___x_1333_) == 6)
{
lean_object* v_val_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_constName_1313_);
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_val_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 0);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v___x_1333_);
v___x_1342_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1343_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1342_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
if (lean_obj_tag(v_a_1344_) == 0)
{
lean_del_object(v___x_1346_);
goto v___jp_1319_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1350_; 
lean_dec(v_constName_1313_);
v_val_1348_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v_a_1344_, 1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_val_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_constName_1313_);
v_a_1353_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1343_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1343_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_dec(v_val_1331_);
goto v___jp_1319_;
}
}
else
{
lean_dec(v___x_1330_);
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1320_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1321_ = 0;
v___x_1322_ = l_Lean_MessageData_ofConstName(v_constName_1313_, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1320_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1325_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_env_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_st_ref_get(v___y_1375_);
v_env_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_env_1378_);
lean_dec(v___x_1377_);
lean_inc(v_constName_1371_);
v___x_1379_ = l_Lean_isInductiveCore_x3f(v_env_1378_, v_constName_1371_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1380_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1381_ = 0;
v___x_1382_ = l_Lean_MessageData_ofConstName(v_constName_1371_, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1385_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_constName_1371_);
v_val_1387_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1379_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_val_1387_);
lean_dec(v___x_1379_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 0);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_val_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1401_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1407_ = l_Lean_stringToMessageData(v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1408_, lean_object* v___x_1409_, uint8_t v_instImplicit_1410_, lean_object* v_projDecls_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
lean_inc(v_n_1408_);
v___x_1417_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1408_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; uint8_t v___x_1462_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1459_ = l_Lean_InductiveVal_numCtors(v_a_1418_);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_dec_eq(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_bool_not(v___x_1461_);
if (v___x_1462_ == 0)
{
v___y_1420_ = v___y_1412_;
v___y_1421_ = v___y_1413_;
v___y_1422_ = v___y_1414_;
v___y_1423_ = v___y_1415_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_a_1418_);
lean_dec_ref(v_projDecls_1411_);
v___x_1463_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1464_ = 0;
v___x_1465_ = l_Lean_MessageData_ofConstName(v_n_1408_, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1463_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1468_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1469_;
}
v___jp_1419_:
{
lean_object* v_toConstantVal_1424_; lean_object* v_numParams_1425_; lean_object* v_ctors_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_toConstantVal_1424_ = lean_ctor_get(v_a_1418_, 0);
lean_inc_ref(v_toConstantVal_1424_);
v_numParams_1425_ = lean_ctor_get(v_a_1418_, 1);
lean_inc(v_numParams_1425_);
v_ctors_1426_ = lean_ctor_get(v_a_1418_, 4);
lean_inc(v_ctors_1426_);
lean_dec(v_a_1418_);
v___x_1427_ = l_List_head_x21___redArg(v___x_1409_, v_ctors_1426_);
lean_dec(v_ctors_1426_);
v___x_1428_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1427_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v_levelParams_1430_; lean_object* v_type_1431_; lean_object* v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v_levelParams_1430_ = lean_ctor_get(v_toConstantVal_1424_, 1);
lean_inc(v_levelParams_1430_);
v_type_1431_ = lean_ctor_get(v_toConstantVal_1424_, 2);
lean_inc_ref(v_type_1431_);
lean_dec_ref(v_toConstantVal_1424_);
v___x_1432_ = l_Lean_Meta_isPropFormerType(v_type_1431_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_toConstantVal_1433_; lean_object* v_a_1434_; lean_object* v_type_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v_toConstantVal_1433_ = lean_ctor_get(v_a_1429_, 0);
lean_inc_ref(v_toConstantVal_1433_);
lean_dec(v_a_1429_);
v_a_1434_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1432_, 1);
v_type_1435_ = lean_ctor_get(v_toConstantVal_1433_, 2);
lean_inc_ref(v_type_1435_);
v___x_1436_ = lean_box(0);
lean_inc(v_levelParams_1430_);
v___x_1437_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1430_, v___x_1436_);
v___x_1438_ = lean_box(v_instImplicit_1410_);
lean_inc(v_numParams_1425_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1439_, 0, v___x_1438_);
lean_closure_set(v___f_1439_, 1, v_projDecls_1411_);
lean_closure_set(v___f_1439_, 2, v_toConstantVal_1433_);
lean_closure_set(v___f_1439_, 3, v_numParams_1425_);
lean_closure_set(v___f_1439_, 4, v___x_1437_);
lean_closure_set(v___f_1439_, 5, v_n_1408_);
lean_closure_set(v___f_1439_, 6, v_levelParams_1430_);
lean_closure_set(v___f_1439_, 7, v_a_1434_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_numParams_1425_);
v___x_1441_ = 0;
v___x_1442_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1435_, v___x_1440_, v___f_1439_, v___x_1441_, v___x_1441_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_levelParams_1430_);
lean_dec(v_a_1429_);
lean_dec(v_numParams_1425_);
lean_dec_ref(v_projDecls_1411_);
lean_dec(v_n_1408_);
v_a_1443_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1432_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1432_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_numParams_1425_);
lean_dec_ref(v_toConstantVal_1424_);
lean_dec_ref(v_projDecls_1411_);
lean_dec(v_n_1408_);
v_a_1451_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1428_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1428_);
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
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v_projDecls_1411_);
lean_dec(v_n_1408_);
v_a_1470_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1417_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1417_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1478_, lean_object* v___x_1479_, lean_object* v_instImplicit_1480_, lean_object* v_projDecls_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v_instImplicit_boxed_1487_; lean_object* v_res_1488_; 
v_instImplicit_boxed_1487_ = lean_unbox(v_instImplicit_1480_);
v_res_1488_ = l_Lean_Meta_mkProjections___lam__2(v_n_1478_, v___x_1479_, v_instImplicit_boxed_1487_, v_projDecls_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___x_1479_);
return v_res_1488_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_unsigned_to_nat(32u);
v___x_1493_ = lean_mk_empty_array_with_capacity(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = ((size_t)5ULL);
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = lean_unsigned_to_nat(32u);
v___x_1498_ = lean_mk_empty_array_with_capacity(v___x_1497_);
v___x_1499_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1500_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___x_1498_);
lean_ctor_set(v___x_1500_, 2, v___x_1496_);
lean_ctor_set(v___x_1500_, 3, v___x_1496_);
lean_ctor_set_usize(v___x_1500_, 4, v___x_1495_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1501_ = lean_box(1);
v___x_1502_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1503_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1502_);
lean_ctor_set(v___x_1504_, 2, v___x_1501_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1507_, lean_object* v_projDecls_1508_, uint8_t v_instImplicit_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_box(v_instImplicit_1509_);
v___f_1517_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1517_, 0, v_n_1507_);
lean_closure_set(v___f_1517_, 1, v___x_1515_);
lean_closure_set(v___f_1517_, 2, v___x_1516_);
lean_closure_set(v___f_1517_, 3, v_projDecls_1508_);
v___x_1518_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1519_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1520_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1518_, v___x_1519_, v___f_1517_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1521_, lean_object* v_projDecls_1522_, lean_object* v_instImplicit_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
uint8_t v_instImplicit_boxed_1529_; lean_object* v_res_1530_; 
v_instImplicit_boxed_1529_ = lean_unbox(v_instImplicit_1523_);
v_res_1530_ = l_Lean_Meta_mkProjections(v_n_1521_, v_projDecls_1522_, v_instImplicit_boxed_1529_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1531_, lean_object* v_as_1532_, size_t v_sz_1533_, size_t v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1531_, v_as_1532_, v_sz_1533_, v_i_1534_, v_b_1535_, v___y_1536_, v___y_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1542_, lean_object* v_as_1543_, lean_object* v_sz_1544_, lean_object* v_i_1545_, lean_object* v_b_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
uint8_t v_instImplicit_boxed_1552_; size_t v_sz_boxed_1553_; size_t v_i_boxed_1554_; lean_object* v_res_1555_; 
v_instImplicit_boxed_1552_ = lean_unbox(v_instImplicit_1542_);
v_sz_boxed_1553_ = lean_unbox_usize(v_sz_1544_);
lean_dec(v_sz_1544_);
v_i_boxed_1554_ = lean_unbox_usize(v_i_1545_);
lean_dec(v_i_1545_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1552_, v_as_1543_, v_sz_boxed_1553_, v_i_boxed_1554_, v_b_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v_as_1543_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1556_, uint8_t v_s_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1556_, v_s_1557_, v___y_1559_, v___y_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1564_, lean_object* v_s_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v_s_boxed_1571_; lean_object* v_res_1572_; 
v_s_boxed_1571_ = lean_unbox(v_s_1565_);
v_res_1572_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1564_, v_s_boxed_1571_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1573_, lean_object* v_ref_1574_, lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1574_, v_msg_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_ref_1583_, lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1582_, v_ref_1583_, v_msg_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v_ref_1583_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1591_, lean_object* v_x_1592_, uint8_t v_isExporting_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1592_, v_isExporting_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_x_1601_, lean_object* v_isExporting_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v_isExporting_boxed_1608_; lean_object* v_res_1609_; 
v_isExporting_boxed_1608_ = lean_unbox(v_isExporting_1602_);
v_res_1609_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1600_, v_x_1601_, v_isExporting_boxed_1608_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1610_, lean_object* v_x_1611_, uint8_t v_when_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1611_, v_when_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_x_1620_, lean_object* v_when_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_when_boxed_1627_; lean_object* v_res_1628_; 
v_when_boxed_1627_ = lean_unbox(v_when_1621_);
v_res_1628_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1619_, v_x_1620_, v_when_boxed_1627_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1629_, lean_object* v_projDecls_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, uint8_t v_instImplicit_1633_, lean_object* v___x_1634_, lean_object* v_params_1635_, lean_object* v_self_1636_, lean_object* v_a_1637_, lean_object* v___x_1638_, lean_object* v_n_1639_, lean_object* v___x_1640_, uint8_t v_a_1641_, lean_object* v_inst_1642_, lean_object* v_R_1643_, lean_object* v_a_1644_, lean_object* v_b_1645_, lean_object* v_c_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1629_, v_projDecls_1630_, v___x_1631_, v___x_1632_, v_instImplicit_1633_, v___x_1634_, v_params_1635_, v_self_1636_, v_a_1637_, v___x_1638_, v_n_1639_, v___x_1640_, v_a_1641_, v_a_1644_, v_b_1645_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1653_ = _args[0];
lean_object* v_projDecls_1654_ = _args[1];
lean_object* v___x_1655_ = _args[2];
lean_object* v___x_1656_ = _args[3];
lean_object* v_instImplicit_1657_ = _args[4];
lean_object* v___x_1658_ = _args[5];
lean_object* v_params_1659_ = _args[6];
lean_object* v_self_1660_ = _args[7];
lean_object* v_a_1661_ = _args[8];
lean_object* v___x_1662_ = _args[9];
lean_object* v_n_1663_ = _args[10];
lean_object* v___x_1664_ = _args[11];
lean_object* v_a_1665_ = _args[12];
lean_object* v_inst_1666_ = _args[13];
lean_object* v_R_1667_ = _args[14];
lean_object* v_a_1668_ = _args[15];
lean_object* v_b_1669_ = _args[16];
lean_object* v_c_1670_ = _args[17];
lean_object* v___y_1671_ = _args[18];
lean_object* v___y_1672_ = _args[19];
lean_object* v___y_1673_ = _args[20];
lean_object* v___y_1674_ = _args[21];
lean_object* v___y_1675_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1676_; uint8_t v_a_20306__boxed_1677_; lean_object* v_res_1678_; 
v_instImplicit_boxed_1676_ = lean_unbox(v_instImplicit_1657_);
v_a_20306__boxed_1677_ = lean_unbox(v_a_1665_);
v_res_1678_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1653_, v_projDecls_1654_, v___x_1655_, v___x_1656_, v_instImplicit_boxed_1676_, v___x_1658_, v_params_1659_, v_self_1660_, v_a_1661_, v___x_1662_, v_n_1663_, v___x_1664_, v_a_20306__boxed_1677_, v_inst_1666_, v_R_1667_, v_a_1668_, v_b_1669_, v_c_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec_ref(v_projDecls_1654_);
lean_dec(v_upperBound_1653_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1679_, uint8_t v_allowLevelAssignments_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1680_, v_k_1679_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1686_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1686_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1686_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1703_, lean_object* v_allowLevelAssignments_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1710_; lean_object* v_res_1711_; 
v_allowLevelAssignments_boxed_1710_ = lean_unbox(v_allowLevelAssignments_1704_);
v_res_1711_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1703_, v_allowLevelAssignments_boxed_1710_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1712_, lean_object* v_k_1713_, uint8_t v_allowLevelAssignments_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1713_, v_allowLevelAssignments_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_k_1722_, lean_object* v_allowLevelAssignments_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1729_; lean_object* v_res_1730_; 
v_allowLevelAssignments_boxed_1729_ = lean_unbox(v_allowLevelAssignments_1723_);
v_res_1730_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1721_, v_k_1722_, v_allowLevelAssignments_boxed_1729_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1731_, size_t v_sz_1732_, size_t v_i_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1733_, v_sz_1732_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1734_);
return v___x_1741_;
}
else
{
lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1797_; 
v_snd_1742_ = lean_ctor_get(v_b_1734_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_b_1734_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v_b_1734_, 0);
lean_dec(v_unused_1798_);
v___x_1744_ = v_b_1734_;
v_isShared_1745_ = v_isSharedCheck_1797_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_dec(v_b_1734_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1797_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_array_1746_; lean_object* v_start_1747_; lean_object* v_stop_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_array_1746_ = lean_ctor_get(v_snd_1742_, 0);
v_start_1747_ = lean_ctor_get(v_snd_1742_, 1);
v_stop_1748_ = lean_ctor_get(v_snd_1742_, 2);
v___x_1749_ = lean_box(0);
v___x_1750_ = lean_nat_dec_lt(v_start_1747_, v_stop_1748_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1752_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1749_);
v___x_1752_ = v___x_1744_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_snd_1742_);
v___x_1752_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1793_; 
lean_inc(v_stop_1748_);
lean_inc(v_start_1747_);
lean_inc_ref(v_array_1746_);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_snd_1742_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; 
v_unused_1794_ = lean_ctor_get(v_snd_1742_, 2);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_snd_1742_, 1);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_snd_1742_, 0);
lean_dec(v_unused_1796_);
v___x_1756_ = v_snd_1742_;
v_isShared_1757_ = v_isSharedCheck_1793_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v_snd_1742_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1793_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1758_ = lean_array_uget_borrowed(v_as_1731_, v_i_1733_);
v___x_1759_ = lean_array_fget_borrowed(v_array_1746_, v_start_1747_);
lean_inc(v___x_1759_);
lean_inc(v_a_1758_);
v___x_1760_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1758_, v___x_1759_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1784_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1784_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1784_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_start_1747_, v___x_1765_);
lean_dec(v_start_1747_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___x_1766_);
v___x_1768_ = v___x_1756_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_array_1746_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_stop_1748_);
v___x_1768_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_unbox(v_a_1761_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_a_1761_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___x_1768_);
lean_ctor_set(v___x_1744_, 0, v___x_1770_);
v___x_1772_ = v___x_1744_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1768_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1772_);
v___x_1774_ = v___x_1763_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
lean_object* v___x_1778_; 
lean_del_object(v___x_1763_);
lean_dec(v_a_1761_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___x_1768_);
lean_ctor_set(v___x_1744_, 0, v___x_1749_);
v___x_1778_ = v___x_1744_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1768_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
size_t v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1733_, v___x_1779_);
v_i_1733_ = v___x_1780_;
v_b_1734_ = v___x_1778_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_del_object(v___x_1756_);
lean_dec(v_stop_1748_);
lean_dec(v_start_1747_);
lean_dec_ref(v_array_1746_);
lean_del_object(v___x_1744_);
v_a_1785_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1760_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1760_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1799_, v_sz_boxed_1808_, v_i_boxed_1809_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_as_1799_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1811_, lean_object* v_params2_1812_, lean_object* v___x_1813_, lean_object* v_params1_1814_, uint8_t v___x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
if (v___x_1811_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec(v___x_1813_);
lean_dec_ref(v_params2_1812_);
v___x_1821_ = lean_box(v___x_1811_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; size_t v_sz_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Array_toSubarray___redArg(v_params2_1812_, v___x_1823_, v___x_1813_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
v_sz_1827_ = lean_array_size(v_params1_1814_);
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1814_, v_sz_1827_, v___x_1828_, v___x_1826_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1843_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1843_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_fst_1834_; 
v_fst_1834_ = lean_ctor_get(v_a_1830_, 0);
lean_inc(v_fst_1834_);
lean_dec(v_a_1830_);
if (lean_obj_tag(v_fst_1834_) == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_box(v___x_1815_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v_val_1839_; lean_object* v___x_1841_; 
v_val_1839_ = lean_ctor_get(v_fst_1834_, 0);
lean_inc(v_val_1839_);
lean_dec_ref_known(v_fst_1834_, 1);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v_val_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_val_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_a_1844_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1829_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1829_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1852_, lean_object* v_params2_1853_, lean_object* v___x_1854_, lean_object* v_params1_1855_, lean_object* v___x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
uint8_t v___x_2097__boxed_1862_; uint8_t v___x_2099__boxed_1863_; lean_object* v_res_1864_; 
v___x_2097__boxed_1862_ = lean_unbox(v___x_1852_);
v___x_2099__boxed_1863_ = lean_unbox(v___x_1856_);
v_res_1864_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2097__boxed_1862_, v_params2_1853_, v___x_1854_, v_params1_1855_, v___x_2099__boxed_1863_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec_ref(v_params1_1855_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1865_, lean_object* v_params2_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___y_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1872_ = lean_array_get_size(v_params1_1865_);
v___x_1873_ = lean_array_get_size(v_params2_1866_);
v___x_1874_ = lean_nat_dec_eq(v___x_1872_, v___x_1873_);
v___x_1875_ = 1;
v___x_1876_ = lean_box(v___x_1874_);
v___x_1877_ = lean_box(v___x_1875_);
v___y_1878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1878_, 0, v___x_1876_);
lean_closure_set(v___y_1878_, 1, v_params2_1866_);
lean_closure_set(v___y_1878_, 2, v___x_1873_);
lean_closure_set(v___y_1878_, 3, v_params1_1865_);
lean_closure_set(v___y_1878_, 4, v___x_1877_);
v___x_1879_ = 0;
v___x_1880_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1878_, v___x_1879_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1881_, lean_object* v_params2_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1881_, v_params2_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_env_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1892_ = lean_st_ref_get(v___y_1890_);
v_env_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_ref(v_env_1893_);
lean_dec(v___x_1892_);
v___x_1894_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1893_, v_declName_1889_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1896_, v___y_1897_);
lean_dec(v___y_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1900_, v___y_1904_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1914_; lean_object* v_dummy_1915_; 
v___x_1914_ = lean_box(0);
v_dummy_1915_ = l_Lean_Expr_sort___override(v___x_1914_);
return v_dummy_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1916_, lean_object* v_induct_1917_, lean_object* v_params_1918_, lean_object* v_idx_1919_, lean_object* v_e_1920_, lean_object* v_x_x3f_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
if (lean_obj_tag(v_e_1920_) == 11)
{
lean_object* v_typeName_1933_; lean_object* v_idx_1934_; lean_object* v_struct_1935_; uint8_t v___y_1983_; uint8_t v___x_1986_; 
v_typeName_1933_ = lean_ctor_get(v_e_1920_, 0);
v_idx_1934_ = lean_ctor_get(v_e_1920_, 1);
v_struct_1935_ = lean_ctor_get(v_e_1920_, 2);
lean_inc_ref(v_struct_1935_);
v___x_1986_ = lean_nat_dec_eq(v_idx_1934_, v_idx_1919_);
if (v___x_1986_ == 0)
{
v___y_1983_ = v___x_1986_;
goto v___jp_1982_;
}
else
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_name_eq(v_induct_1917_, v_typeName_1933_);
v___y_1983_ = v___x_1987_;
goto v___jp_1982_;
}
v___jp_1936_:
{
lean_object* v___x_1937_; 
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
v___x_1937_ = lean_infer_type(v_e_1920_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
v___x_1939_ = lean_whnf(v_a_1938_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v_dummy_1941_; lean_object* v_nargs_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v_dummy_1941_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1942_ = l_Lean_Expr_getAppNumArgs(v_a_1940_);
lean_inc(v_nargs_1942_);
v___x_1943_ = lean_mk_array(v_nargs_1942_, v_dummy_1941_);
v___x_1944_ = lean_unsigned_to_nat(1u);
v___x_1945_ = lean_nat_sub(v_nargs_1942_, v___x_1944_);
lean_dec(v_nargs_1942_);
v___x_1946_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1940_, v___x_1943_, v___x_1945_);
v___x_1947_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1918_, v___x_1946_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1957_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1957_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1957_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1952_ == 0)
{
lean_del_object(v___x_1950_);
lean_dec_ref(v_struct_1935_);
goto v___jp_1927_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_struct_1935_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1953_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
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
lean_dec_ref(v_struct_1935_);
v_a_1958_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1947_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1947_);
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
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_struct_1935_);
lean_dec_ref(v_params_1918_);
v_a_1966_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1939_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1939_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_struct_1935_);
lean_dec_ref(v_params_1918_);
v_a_1974_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1937_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1937_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
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
v___jp_1982_:
{
if (v___y_1983_ == 0)
{
lean_dec_ref(v_struct_1935_);
lean_dec_ref_known(v_e_1920_, 3);
lean_dec_ref(v_params_1918_);
goto v___jp_1927_;
}
else
{
if (lean_obj_tag(v_x_x3f_1921_) == 0)
{
goto v___jp_1936_;
}
else
{
lean_object* v_val_1984_; uint8_t v___x_1985_; 
v_val_1984_ = lean_ctor_get(v_x_x3f_1921_, 0);
v___x_1985_ = lean_expr_eqv(v_val_1984_, v_struct_1935_);
if (v___x_1985_ == 0)
{
lean_dec_ref(v_struct_1935_);
lean_dec_ref_known(v_e_1920_, 3);
lean_dec_ref(v_params_1918_);
goto v___jp_1927_;
}
else
{
goto v___jp_1936_;
}
}
}
}
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Expr_getAppFn(v_e_1920_);
if (lean_obj_tag(v___x_1988_) == 4)
{
lean_object* v_declName_1989_; lean_object* v___x_1990_; lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2040_; 
v_declName_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_declName_1989_);
lean_dec_ref_known(v___x_1988_, 2);
v___x_1990_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1989_, v_a_1925_);
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2040_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2040_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___y_1996_; lean_object* v___y_1997_; 
if (lean_obj_tag(v_a_1991_) == 1)
{
lean_object* v_val_2025_; lean_object* v_ctorName_2026_; lean_object* v_numParams_2027_; lean_object* v_i_2028_; uint8_t v___y_2030_; uint8_t v___x_2038_; 
v_val_2025_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_val_2025_);
lean_dec_ref_known(v_a_1991_, 1);
v_ctorName_2026_ = lean_ctor_get(v_val_2025_, 0);
lean_inc(v_ctorName_2026_);
v_numParams_2027_ = lean_ctor_get(v_val_2025_, 1);
lean_inc(v_numParams_2027_);
v_i_2028_ = lean_ctor_get(v_val_2025_, 2);
lean_inc(v_i_2028_);
lean_dec(v_val_2025_);
v___x_2038_ = lean_name_eq(v_ctorName_2026_, v_ctor_1916_);
lean_dec(v_ctorName_2026_);
if (v___x_2038_ == 0)
{
lean_dec(v_i_2028_);
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
else
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_nat_dec_eq(v_i_2028_, v_idx_1919_);
lean_dec(v_i_2028_);
v___y_2030_ = v___x_2039_;
goto v___jp_2029_;
}
v___jp_2029_:
{
if (v___y_2030_ == 0)
{
lean_dec(v_numParams_2027_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_params_1918_);
goto v___jp_1930_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2031_ = l_Lean_Expr_getAppNumArgs(v_e_1920_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_numParams_2027_, v___x_2032_);
lean_dec(v_numParams_2027_);
v___x_2034_ = lean_nat_dec_eq(v___x_2031_, v___x_2033_);
lean_dec(v___x_2033_);
lean_dec(v___x_2031_);
if (v___x_2034_ == 0)
{
lean_del_object(v___x_1993_);
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_params_1918_);
goto v___jp_1930_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_Expr_appArg_x21(v_e_1920_);
if (lean_obj_tag(v_x_x3f_1921_) == 0)
{
v___y_1996_ = v___x_2035_;
v___y_1997_ = v___x_2032_;
goto v___jp_1995_;
}
else
{
lean_object* v_val_2036_; uint8_t v___x_2037_; 
v_val_2036_ = lean_ctor_get(v_x_x3f_1921_, 0);
v___x_2037_ = lean_expr_eqv(v_val_2036_, v___x_2035_);
if (v___x_2037_ == 0)
{
lean_dec_ref(v___x_2035_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_params_1918_);
goto v___jp_1930_;
}
else
{
v___y_1996_ = v___x_2035_;
v___y_1997_ = v___x_2032_;
goto v___jp_1995_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1993_);
lean_dec(v_a_1991_);
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_params_1918_);
goto v___jp_1930_;
}
v___jp_1995_:
{
lean_object* v___x_1998_; lean_object* v_dummy_1999_; lean_object* v_nargs_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_1998_ = l_Lean_Expr_appFn_x21(v_e_1920_);
lean_dec_ref(v_e_1920_);
v_dummy_1999_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2000_ = l_Lean_Expr_getAppNumArgs(v___x_1998_);
lean_inc(v_nargs_2000_);
v___x_2001_ = lean_mk_array(v_nargs_2000_, v_dummy_1999_);
v___x_2002_ = lean_nat_sub(v_nargs_2000_, v___y_1997_);
lean_dec(v_nargs_2000_);
v___x_2003_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1998_, v___x_2001_, v___x_2002_);
v___x_2004_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1918_, v___x_2003_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2016_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2016_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2016_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2009_ == 0)
{
lean_del_object(v___x_2007_);
lean_dec_ref(v___y_1996_);
lean_del_object(v___x_1993_);
goto v___jp_1930_;
}
else
{
lean_object* v___x_2011_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 1);
lean_ctor_set(v___x_1993_, 0, v___y_1996_);
v___x_2011_ = v___x_1993_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___y_1996_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v___y_1996_);
lean_del_object(v___x_1993_);
v_a_2017_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2004_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2004_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_e_1920_);
lean_dec_ref(v_params_1918_);
goto v___jp_1930_;
}
}
v___jp_1927_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
v___jp_1930_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2041_, lean_object* v_induct_2042_, lean_object* v_params_2043_, lean_object* v_idx_2044_, lean_object* v_e_2045_, lean_object* v_x_x3f_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2041_, v_induct_2042_, v_params_2043_, v_idx_2044_, v_e_2045_, v_x_x3f_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_a_2047_);
lean_dec(v_x_x3f_2046_);
lean_dec(v_idx_2044_);
lean_dec(v_induct_2042_);
lean_dec(v_ctor_2041_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v_env_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2059_ = lean_st_ref_get(v___y_2057_);
v_env_2063_ = lean_ctor_get(v___x_2059_, 0);
lean_inc_ref(v_env_2063_);
lean_dec(v___x_2059_);
v___x_2064_ = 0;
v___x_2065_ = l_Lean_Environment_findAsync_x3f(v_env_2063_, v_constName_2053_, v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2085_; 
v_val_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2085_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_val_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2085_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
uint8_t v_kind_2070_; 
v_kind_2070_ = lean_ctor_get_uint8(v_val_2066_, sizeof(void*)*3);
if (v_kind_2070_ == 6)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2066_);
if (lean_obj_tag(v___x_2071_) == 6)
{
lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2082_; 
v_val_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v_val_2072_);
v___x_2077_ = v___x_2068_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_val_2072_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v___x_2071_);
lean_del_object(v___x_2068_);
v___x_2083_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2084_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2083_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2084_;
}
}
else
{
lean_del_object(v___x_2068_);
lean_dec(v_val_2066_);
goto v___jp_2060_;
}
}
}
else
{
lean_dec(v___x_2065_);
goto v___jp_2060_;
}
v___jp_2060_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2101_, lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v_declName_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v_a_2107_, lean_object* v_val_2108_, lean_object* v_a_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v___x_2116_; 
v___x_2116_ = lean_nat_dec_lt(v_a_2109_, v_upperBound_2101_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v_a_2109_);
lean_dec_ref(v___x_2106_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_b_2110_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_b_2110_);
v___x_2118_ = l_Lean_instInhabitedExpr;
v___x_2119_ = lean_nat_add(v___x_2102_, v_a_2109_);
v___x_2120_ = lean_array_get_borrowed(v___x_2118_, v___x_2103_, v___x_2119_);
lean_dec(v___x_2119_);
lean_inc(v___x_2120_);
lean_inc_ref(v___x_2106_);
v___x_2121_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2104_, v___x_2105_, v___x_2106_, v_a_2109_, v___x_2120_, v_a_2107_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2140_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2126_; uint8_t v___x_2127_; 
v_val_2126_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_a_2122_, 1);
v___x_2127_ = lean_expr_eqv(v_val_2126_, v_val_2108_);
lean_dec(v_val_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec(v_a_2109_);
lean_dec_ref(v___x_2106_);
v___x_2128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2128_);
v___x_2130_ = v___x_2124_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_del_object(v___x_2124_);
v___x_2132_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_add(v_a_2109_, v___x_2133_);
lean_dec(v_a_2109_);
v_a_2109_ = v___x_2134_;
v_b_2110_ = v___x_2132_;
goto _start;
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v_a_2122_);
lean_dec(v_a_2109_);
lean_dec_ref(v___x_2106_);
v___x_2136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2136_);
v___x_2138_ = v___x_2124_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_a_2109_);
lean_dec_ref(v___x_2106_);
v_a_2141_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2121_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2121_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2149_, lean_object* v___x_2150_, lean_object* v___x_2151_, lean_object* v_declName_2152_, lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v_a_2155_, lean_object* v_val_2156_, lean_object* v_a_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2149_, v___x_2150_, v___x_2151_, v_declName_2152_, v___x_2153_, v___x_2154_, v_a_2155_, v_val_2156_, v_a_2157_, v_b_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v_val_2156_);
lean_dec(v_a_2155_);
lean_dec(v___x_2153_);
lean_dec(v_declName_2152_);
lean_dec_ref(v___x_2151_);
lean_dec(v___x_2150_);
lean_dec(v_upperBound_2149_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2165_, lean_object* v_p_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Expr_getAppFn(v_e_2165_);
if (lean_obj_tag(v___x_2172_) == 4)
{
lean_object* v_declName_2173_; lean_object* v___x_2174_; 
v_declName_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_n(v_declName_2173_, 2);
lean_dec_ref_known(v___x_2172_, 2);
v___x_2174_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2173_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2247_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2247_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2247_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2179_; lean_object* v_induct_2180_; lean_object* v_numParams_2181_; lean_object* v_numFields_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_val_2179_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v_a_2175_, 1);
v_induct_2180_ = lean_ctor_get(v_val_2179_, 1);
lean_inc_n(v_induct_2180_, 2);
v_numParams_2181_ = lean_ctor_get(v_val_2179_, 3);
lean_inc(v_numParams_2181_);
v_numFields_2182_ = lean_ctor_get(v_val_2179_, 4);
lean_inc(v_numFields_2182_);
lean_dec(v_val_2179_);
v___x_2183_ = lean_apply_1(v_p_2166_, v_induct_2180_);
v___x_2184_ = lean_unbox(v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec(v_numFields_2182_);
lean_dec(v_numParams_2181_);
lean_dec(v_induct_2180_);
lean_dec(v_declName_2173_);
lean_dec_ref(v_e_2165_);
v___x_2185_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2185_);
v___x_2187_ = v___x_2177_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
else
{
lean_object* v___x_2189_; uint8_t v___y_2191_; uint8_t v___x_2239_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_nat_dec_lt(v___x_2189_, v_numFields_2182_);
if (v___x_2239_ == 0)
{
v___y_2191_ = v___x_2239_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2240_ = l_Lean_Expr_getAppNumArgs(v_e_2165_);
v___x_2241_ = lean_nat_add(v_numParams_2181_, v_numFields_2182_);
v___x_2242_ = lean_nat_dec_eq(v___x_2240_, v___x_2241_);
lean_dec(v___x_2241_);
lean_dec(v___x_2240_);
v___y_2191_ = v___x_2242_;
goto v___jp_2190_;
}
v___jp_2190_:
{
if (v___y_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
lean_dec(v_numFields_2182_);
lean_dec(v_numParams_2181_);
lean_dec(v_induct_2180_);
lean_dec(v_declName_2173_);
lean_dec_ref(v_e_2165_);
v___x_2192_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2192_);
v___x_2194_ = v___x_2177_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
else
{
lean_object* v_dummy_2196_; lean_object* v_nargs_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_del_object(v___x_2177_);
v_dummy_2196_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2197_ = l_Lean_Expr_getAppNumArgs(v_e_2165_);
lean_inc(v_nargs_2197_);
v___x_2198_ = lean_mk_array(v_nargs_2197_, v_dummy_2196_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_sub(v_nargs_2197_, v___x_2199_);
lean_dec(v_nargs_2197_);
v___x_2201_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2165_, v___x_2198_, v___x_2200_);
lean_inc(v_numParams_2181_);
v___x_2202_ = l_Array_extract___redArg(v___x_2201_, v___x_2189_, v_numParams_2181_);
v___x_2203_ = l_Lean_instInhabitedExpr;
v___x_2204_ = lean_array_get(v___x_2203_, v___x_2201_, v_numParams_2181_);
v___x_2205_ = lean_box(0);
lean_inc_ref(v___x_2202_);
v___x_2206_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2173_, v_induct_2180_, v___x_2202_, v___x_2189_, v___x_2204_, v___x_2205_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2238_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2238_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2238_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
if (lean_obj_tag(v_a_2207_) == 1)
{
lean_object* v_val_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_del_object(v___x_2209_);
v_val_2211_ = lean_ctor_get(v_a_2207_, 0);
v___x_2212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2182_, v_numParams_2181_, v___x_2201_, v_declName_2173_, v_induct_2180_, v___x_2202_, v_a_2207_, v_val_2211_, v___x_2199_, v___x_2212_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_induct_2180_);
lean_dec(v_declName_2173_);
lean_dec_ref(v___x_2201_);
lean_dec(v_numParams_2181_);
lean_dec(v_numFields_2182_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2226_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2226_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2226_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_fst_2218_; 
v_fst_2218_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_fst_2218_);
lean_dec(v_a_2214_);
if (lean_obj_tag(v_fst_2218_) == 0)
{
lean_object* v___x_2220_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_a_2207_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2207_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v_val_2222_; lean_object* v___x_2224_; 
lean_dec_ref_known(v_a_2207_, 1);
v_val_2222_ = lean_ctor_get(v_fst_2218_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v_fst_2218_, 1);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v_val_2222_);
v___x_2224_ = v___x_2216_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_val_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref_known(v_a_2207_, 1);
v_a_2227_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2213_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2213_);
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
lean_object* v___x_2236_; 
lean_dec(v_a_2207_);
lean_dec_ref(v___x_2202_);
lean_dec_ref(v___x_2201_);
lean_dec(v_numFields_2182_);
lean_dec(v_numParams_2181_);
lean_dec(v_induct_2180_);
lean_dec(v_declName_2173_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2205_);
v___x_2236_ = v___x_2209_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2205_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_dec_ref(v___x_2202_);
lean_dec_ref(v___x_2201_);
lean_dec(v_numFields_2182_);
lean_dec(v_numParams_2181_);
lean_dec(v_induct_2180_);
lean_dec(v_declName_2173_);
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v_a_2175_);
lean_dec(v_declName_2173_);
lean_dec_ref(v_p_2166_);
lean_dec_ref(v_e_2165_);
v___x_2243_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2243_);
v___x_2245_ = v___x_2177_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_declName_2173_);
lean_dec_ref(v_p_2166_);
lean_dec_ref(v_e_2165_);
v_a_2248_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2174_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2174_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_p_2166_);
lean_dec_ref(v_e_2165_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2258_, lean_object* v_p_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Meta_etaStruct_x3f(v_e_2258_, v_p_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2266_, lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v_declName_2269_, lean_object* v___x_2270_, lean_object* v___x_2271_, lean_object* v_a_2272_, lean_object* v_val_2273_, lean_object* v_inst_2274_, lean_object* v_R_2275_, lean_object* v_a_2276_, lean_object* v_b_2277_, lean_object* v_c_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2266_, v___x_2267_, v___x_2268_, v_declName_2269_, v___x_2270_, v___x_2271_, v_a_2272_, v_val_2273_, v_a_2276_, v_b_2277_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2285_ = _args[0];
lean_object* v___x_2286_ = _args[1];
lean_object* v___x_2287_ = _args[2];
lean_object* v_declName_2288_ = _args[3];
lean_object* v___x_2289_ = _args[4];
lean_object* v___x_2290_ = _args[5];
lean_object* v_a_2291_ = _args[6];
lean_object* v_val_2292_ = _args[7];
lean_object* v_inst_2293_ = _args[8];
lean_object* v_R_2294_ = _args[9];
lean_object* v_a_2295_ = _args[10];
lean_object* v_b_2296_ = _args[11];
lean_object* v_c_2297_ = _args[12];
lean_object* v___y_2298_ = _args[13];
lean_object* v___y_2299_ = _args[14];
lean_object* v___y_2300_ = _args[15];
lean_object* v___y_2301_ = _args[16];
lean_object* v___y_2302_ = _args[17];
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2285_, v___x_2286_, v___x_2287_, v_declName_2288_, v___x_2289_, v___x_2290_, v_a_2291_, v_val_2292_, v_inst_2293_, v_R_2294_, v_a_2295_, v_b_2296_, v_c_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_val_2292_);
lean_dec(v_a_2291_);
lean_dec(v___x_2289_);
lean_dec(v_declName_2288_);
lean_dec_ref(v___x_2287_);
lean_dec(v___x_2286_);
lean_dec(v_upperBound_2285_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = l_Lean_Expr_hasMVar(v_e_2304_);
v___x_2308_ = lean_bool_not(v___x_2307_);
if (v___x_2308_ == 0)
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
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_e_2304_);
return v___x_2329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2330_, v___y_2331_);
lean_dec(v___y_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2334_, v___y_2336_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_x_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2365_, lean_object* v_e_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Meta_etaStruct_x3f(v_e_2366_, v_p_2365_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2392_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2392_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2392_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
if (lean_obj_tag(v_a_2373_) == 1)
{
lean_object* v_val_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2387_; 
v_val_2377_ = lean_ctor_get(v_a_2373_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2379_ = v_a_2373_;
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_val_2377_);
lean_dec(v_a_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2387_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 0);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_val_2377_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2382_);
v___x_2384_ = v___x_2375_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec(v_a_2373_);
v___x_2388_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2388_);
v___x_2390_ = v___x_2375_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_a_2393_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2372_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2372_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2401_, lean_object* v_e_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2401_, v_e_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_apply_1(v_x_2410_, lean_box(0));
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2418_, v_x_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2426_, lean_object* v_b_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
lean_dec(v_b_2427_);
lean_dec_ref(v_a_2426_);
return v_x_2428_;
}
else
{
lean_object* v_key_2429_; lean_object* v_value_2430_; lean_object* v_tail_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2443_; 
v_key_2429_ = lean_ctor_get(v_x_2428_, 0);
v_value_2430_ = lean_ctor_get(v_x_2428_, 1);
v_tail_2431_ = lean_ctor_get(v_x_2428_, 2);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2433_ = v_x_2428_;
v_isShared_2434_ = v_isSharedCheck_2443_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_tail_2431_);
lean_inc(v_value_2430_);
lean_inc(v_key_2429_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2443_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
uint8_t v___x_2435_; 
v___x_2435_ = l_Lean_ExprStructEq_beq(v_key_2429_, v_a_2426_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2426_, v_b_2427_, v_tail_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v___x_2436_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_key_2429_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_value_2430_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
else
{
lean_object* v___x_2441_; 
lean_dec(v_value_2430_);
lean_dec(v_key_2429_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 1, v_b_2427_);
lean_ctor_set(v___x_2433_, 0, v_a_2426_);
v___x_2441_ = v___x_2433_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2426_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_b_2427_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_tail_2431_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
return v_x_2444_;
}
else
{
lean_object* v_key_2446_; lean_object* v_value_2447_; lean_object* v_tail_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2471_; 
v_key_2446_ = lean_ctor_get(v_x_2445_, 0);
v_value_2447_ = lean_ctor_get(v_x_2445_, 1);
v_tail_2448_ = lean_ctor_get(v_x_2445_, 2);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_x_2445_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2450_ = v_x_2445_;
v_isShared_2451_ = v_isSharedCheck_2471_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_tail_2448_);
lean_inc(v_value_2447_);
lean_inc(v_key_2446_);
lean_dec(v_x_2445_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2471_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; uint64_t v___x_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; uint64_t v_fold_2456_; uint64_t v___x_2457_; uint64_t v___x_2458_; uint64_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; size_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2452_ = lean_array_get_size(v_x_2444_);
v___x_2453_ = l_Lean_ExprStructEq_hash(v_key_2446_);
v___x_2454_ = 32ULL;
v___x_2455_ = lean_uint64_shift_right(v___x_2453_, v___x_2454_);
v_fold_2456_ = lean_uint64_xor(v___x_2453_, v___x_2455_);
v___x_2457_ = 16ULL;
v___x_2458_ = lean_uint64_shift_right(v_fold_2456_, v___x_2457_);
v___x_2459_ = lean_uint64_xor(v_fold_2456_, v___x_2458_);
v___x_2460_ = lean_uint64_to_usize(v___x_2459_);
v___x_2461_ = lean_usize_of_nat(v___x_2452_);
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_sub(v___x_2461_, v___x_2462_);
v___x_2464_ = lean_usize_land(v___x_2460_, v___x_2463_);
v___x_2465_ = lean_array_uget_borrowed(v_x_2444_, v___x_2464_);
lean_inc(v___x_2465_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 2, v___x_2465_);
v___x_2467_ = v___x_2450_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_key_2446_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_value_2447_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_array_uset(v_x_2444_, v___x_2464_, v___x_2467_);
v_x_2444_ = v___x_2468_;
v_x_2445_ = v_tail_2448_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2472_, lean_object* v_source_2473_, lean_object* v_target_2474_){
_start:
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = lean_array_get_size(v_source_2473_);
v___x_2476_ = lean_nat_dec_lt(v_i_2472_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v_source_2473_);
lean_dec(v_i_2472_);
return v_target_2474_;
}
else
{
lean_object* v_es_2477_; lean_object* v___x_2478_; lean_object* v_source_2479_; lean_object* v_target_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_es_2477_ = lean_array_fget(v_source_2473_, v_i_2472_);
v___x_2478_ = lean_box(0);
v_source_2479_ = lean_array_fset(v_source_2473_, v_i_2472_, v___x_2478_);
v_target_2480_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2474_, v_es_2477_);
v___x_2481_ = lean_unsigned_to_nat(1u);
v___x_2482_ = lean_nat_add(v_i_2472_, v___x_2481_);
lean_dec(v_i_2472_);
v_i_2472_ = v___x_2482_;
v_source_2473_ = v_source_2479_;
v_target_2474_ = v_target_2480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_nbuckets_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2485_ = lean_array_get_size(v_data_2484_);
v___x_2486_ = lean_unsigned_to_nat(2u);
v_nbuckets_2487_ = lean_nat_mul(v___x_2485_, v___x_2486_);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_box(0);
v___x_2490_ = lean_mk_array(v_nbuckets_2487_, v___x_2489_);
v___x_2491_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2488_, v_data_2484_, v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2492_, lean_object* v_x_2493_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
else
{
lean_object* v_key_2495_; lean_object* v_tail_2496_; uint8_t v___x_2497_; 
v_key_2495_ = lean_ctor_get(v_x_2493_, 0);
v_tail_2496_ = lean_ctor_get(v_x_2493_, 2);
v___x_2497_ = l_Lean_ExprStructEq_beq(v_key_2495_, v_a_2492_);
if (v___x_2497_ == 0)
{
v_x_2493_ = v_tail_2496_;
goto _start;
}
else
{
return v___x_2497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2499_, lean_object* v_x_2500_){
_start:
{
uint8_t v_res_2501_; lean_object* v_r_2502_; 
v_res_2501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2499_, v_x_2500_);
lean_dec(v_x_2500_);
lean_dec_ref(v_a_2499_);
v_r_2502_ = lean_box(v_res_2501_);
return v_r_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2503_, lean_object* v_a_2504_, lean_object* v_b_2505_){
_start:
{
lean_object* v_size_2506_; lean_object* v_buckets_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2550_; 
v_size_2506_ = lean_ctor_get(v_m_2503_, 0);
v_buckets_2507_ = lean_ctor_get(v_m_2503_, 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_m_2503_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2509_ = v_m_2503_;
v_isShared_2510_ = v_isSharedCheck_2550_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_buckets_2507_);
lean_inc(v_size_2506_);
lean_dec(v_m_2503_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2550_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; uint64_t v___x_2512_; uint64_t v___x_2513_; uint64_t v___x_2514_; uint64_t v_fold_2515_; uint64_t v___x_2516_; uint64_t v___x_2517_; uint64_t v___x_2518_; size_t v___x_2519_; size_t v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; size_t v___x_2523_; lean_object* v_bkt_2524_; uint8_t v___x_2525_; 
v___x_2511_ = lean_array_get_size(v_buckets_2507_);
v___x_2512_ = l_Lean_ExprStructEq_hash(v_a_2504_);
v___x_2513_ = 32ULL;
v___x_2514_ = lean_uint64_shift_right(v___x_2512_, v___x_2513_);
v_fold_2515_ = lean_uint64_xor(v___x_2512_, v___x_2514_);
v___x_2516_ = 16ULL;
v___x_2517_ = lean_uint64_shift_right(v_fold_2515_, v___x_2516_);
v___x_2518_ = lean_uint64_xor(v_fold_2515_, v___x_2517_);
v___x_2519_ = lean_uint64_to_usize(v___x_2518_);
v___x_2520_ = lean_usize_of_nat(v___x_2511_);
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_sub(v___x_2520_, v___x_2521_);
v___x_2523_ = lean_usize_land(v___x_2519_, v___x_2522_);
v_bkt_2524_ = lean_array_uget_borrowed(v_buckets_2507_, v___x_2523_);
v___x_2525_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2504_, v_bkt_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v_size_x27_2527_; lean_object* v___x_2528_; lean_object* v_buckets_x27_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2526_ = lean_unsigned_to_nat(1u);
v_size_x27_2527_ = lean_nat_add(v_size_2506_, v___x_2526_);
lean_dec(v_size_2506_);
lean_inc(v_bkt_2524_);
v___x_2528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2528_, 0, v_a_2504_);
lean_ctor_set(v___x_2528_, 1, v_b_2505_);
lean_ctor_set(v___x_2528_, 2, v_bkt_2524_);
v_buckets_x27_2529_ = lean_array_uset(v_buckets_2507_, v___x_2523_, v___x_2528_);
v___x_2530_ = lean_unsigned_to_nat(4u);
v___x_2531_ = lean_nat_mul(v_size_x27_2527_, v___x_2530_);
v___x_2532_ = lean_unsigned_to_nat(3u);
v___x_2533_ = lean_nat_div(v___x_2531_, v___x_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_array_get_size(v_buckets_x27_2529_);
v___x_2535_ = lean_nat_dec_le(v___x_2533_, v___x_2534_);
lean_dec(v___x_2533_);
if (v___x_2535_ == 0)
{
lean_object* v_val_2536_; lean_object* v___x_2538_; 
v_val_2536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2529_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_val_2536_);
lean_ctor_set(v___x_2509_, 0, v_size_x27_2527_);
v___x_2538_ = v___x_2509_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_size_x27_2527_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_val_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2541_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_buckets_x27_2529_);
lean_ctor_set(v___x_2509_, 0, v_size_x27_2527_);
v___x_2541_ = v___x_2509_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_size_x27_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_buckets_x27_2529_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_object* v___x_2543_; lean_object* v_buckets_x27_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_inc(v_bkt_2524_);
v___x_2543_ = lean_box(0);
v_buckets_x27_2544_ = lean_array_uset(v_buckets_2507_, v___x_2523_, v___x_2543_);
v___x_2545_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2504_, v_b_2505_, v_bkt_2524_);
v___x_2546_ = lean_array_uset(v_buckets_x27_2544_, v___x_2523_, v___x_2545_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v___x_2546_);
v___x_2548_ = v___x_2509_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_size_2506_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2551_, lean_object* v_e_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2555_ = lean_st_ref_take(v_a_2551_);
v___x_2556_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2555_, v_e_2552_, v_a_2553_);
v___x_2557_ = lean_st_ref_set(v_a_2551_, v___x_2556_);
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2559_, lean_object* v_e_2560_, lean_object* v_a_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2559_, v_e_2560_, v_a_2561_);
lean_dec(v_a_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_apply_1(v_x_2565_, lean_box(0));
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_x_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2573_, v_x_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2581_, lean_object* v_x_2582_){
_start:
{
if (lean_obj_tag(v_x_2582_) == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_box(0);
return v___x_2583_;
}
else
{
lean_object* v_key_2584_; lean_object* v_value_2585_; lean_object* v_tail_2586_; uint8_t v___x_2587_; 
v_key_2584_ = lean_ctor_get(v_x_2582_, 0);
v_value_2585_ = lean_ctor_get(v_x_2582_, 1);
v_tail_2586_ = lean_ctor_get(v_x_2582_, 2);
v___x_2587_ = l_Lean_ExprStructEq_beq(v_key_2584_, v_a_2581_);
if (v___x_2587_ == 0)
{
v_x_2582_ = v_tail_2586_;
goto _start;
}
else
{
lean_object* v___x_2589_; 
lean_inc(v_value_2585_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_value_2585_);
return v___x_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2590_, lean_object* v_x_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2590_, v_x_2591_);
lean_dec(v_x_2591_);
lean_dec_ref(v_a_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_buckets_2595_; lean_object* v___x_2596_; uint64_t v___x_2597_; uint64_t v___x_2598_; uint64_t v___x_2599_; uint64_t v_fold_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; uint64_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_buckets_2595_ = lean_ctor_get(v_m_2593_, 1);
v___x_2596_ = lean_array_get_size(v_buckets_2595_);
v___x_2597_ = l_Lean_ExprStructEq_hash(v_a_2594_);
v___x_2598_ = 32ULL;
v___x_2599_ = lean_uint64_shift_right(v___x_2597_, v___x_2598_);
v_fold_2600_ = lean_uint64_xor(v___x_2597_, v___x_2599_);
v___x_2601_ = 16ULL;
v___x_2602_ = lean_uint64_shift_right(v_fold_2600_, v___x_2601_);
v___x_2603_ = lean_uint64_xor(v_fold_2600_, v___x_2602_);
v___x_2604_ = lean_uint64_to_usize(v___x_2603_);
v___x_2605_ = lean_usize_of_nat(v___x_2596_);
v___x_2606_ = ((size_t)1ULL);
v___x_2607_ = lean_usize_sub(v___x_2605_, v___x_2606_);
v___x_2608_ = lean_usize_land(v___x_2604_, v___x_2607_);
v___x_2609_ = lean_array_uget_borrowed(v_buckets_2595_, v___x_2608_);
v___x_2610_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2594_, v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2611_, lean_object* v_a_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2611_, v_a_2612_);
lean_dec_ref(v_a_2612_);
lean_dec_ref(v_m_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2614_, lean_object* v___y_2615_, lean_object* v_b_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
lean_inc(v___y_2620_);
lean_inc_ref(v___y_2619_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2615_);
v___x_2622_ = lean_apply_7(v_k_2614_, v_b_2616_, v___y_2615_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, lean_box(0));
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2623_, lean_object* v___y_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2623_, v___y_2624_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2624_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2632_, uint8_t v_bi_2633_, lean_object* v_type_2634_, lean_object* v_k_2635_, uint8_t v_kind_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___f_2643_; lean_object* v___x_2644_; 
lean_inc(v___y_2637_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2643_, 0, v_k_2635_);
lean_closure_set(v___f_2643_, 1, v___y_2637_);
v___x_2644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2632_, v_bi_2633_, v_type_2634_, v___f_2643_, v_kind_2636_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2644_) == 0)
{
return v___x_2644_;
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2653_, lean_object* v_bi_2654_, lean_object* v_type_2655_, lean_object* v_k_2656_, lean_object* v_kind_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v_bi_boxed_2664_; uint8_t v_kind_boxed_2665_; lean_object* v_res_2666_; 
v_bi_boxed_2664_ = lean_unbox(v_bi_2654_);
v_kind_boxed_2665_ = lean_unbox(v_kind_2657_);
v_res_2666_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2653_, v_bi_boxed_2664_, v_type_2655_, v_k_2656_, v_kind_boxed_2665_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2667_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2681_, lean_object* v_type_2682_, lean_object* v_val_2683_, lean_object* v_k_2684_, uint8_t v_nondep_2685_, uint8_t v_kind_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___f_2693_; lean_object* v___x_2694_; 
lean_inc(v___y_2687_);
v___f_2693_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2693_, 0, v_k_2684_);
lean_closure_set(v___f_2693_, 1, v___y_2687_);
v___x_2694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2681_, v_type_2682_, v_val_2683_, v___f_2693_, v_nondep_2685_, v_kind_2686_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2694_) == 0)
{
return v___x_2694_;
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2703_, lean_object* v_type_2704_, lean_object* v_val_2705_, lean_object* v_k_2706_, lean_object* v_nondep_2707_, lean_object* v_kind_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v_nondep_boxed_2715_; uint8_t v_kind_boxed_2716_; lean_object* v_res_2717_; 
v_nondep_boxed_2715_ = lean_unbox(v_nondep_2707_);
v_kind_boxed_2716_ = lean_unbox(v_kind_2708_);
v_res_2717_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2703_, v_type_2704_, v_val_2705_, v_k_2706_, v_nondep_boxed_2715_, v_kind_boxed_2716_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
return v_res_2717_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = l_Lean_maxRecDepthErrorMessage;
v___x_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2726_ = l_Lean_MessageData_ofFormat(v___x_2725_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2728_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2729_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v_ref_2730_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___y_2746_; lean_object* v_fileName_2755_; lean_object* v_fileMap_2756_; lean_object* v_options_2757_; lean_object* v_currRecDepth_2758_; lean_object* v_maxRecDepth_2759_; lean_object* v_ref_2760_; lean_object* v_currNamespace_2761_; lean_object* v_openDecls_2762_; lean_object* v_initHeartbeats_2763_; lean_object* v_maxHeartbeats_2764_; lean_object* v_quotContext_2765_; lean_object* v_currMacroScope_2766_; uint8_t v_diag_2767_; lean_object* v_cancelTk_x3f_2768_; uint8_t v_suppressElabErrors_2769_; lean_object* v_inheritedTraceOptions_2770_; uint8_t v___y_2772_; lean_object* v___x_2778_; uint8_t v___x_2779_; uint8_t v___x_2780_; 
v_fileName_2755_ = lean_ctor_get(v___y_2742_, 0);
v_fileMap_2756_ = lean_ctor_get(v___y_2742_, 1);
v_options_2757_ = lean_ctor_get(v___y_2742_, 2);
v_currRecDepth_2758_ = lean_ctor_get(v___y_2742_, 3);
v_maxRecDepth_2759_ = lean_ctor_get(v___y_2742_, 4);
v_ref_2760_ = lean_ctor_get(v___y_2742_, 5);
v_currNamespace_2761_ = lean_ctor_get(v___y_2742_, 6);
v_openDecls_2762_ = lean_ctor_get(v___y_2742_, 7);
v_initHeartbeats_2763_ = lean_ctor_get(v___y_2742_, 8);
v_maxHeartbeats_2764_ = lean_ctor_get(v___y_2742_, 9);
v_quotContext_2765_ = lean_ctor_get(v___y_2742_, 10);
v_currMacroScope_2766_ = lean_ctor_get(v___y_2742_, 11);
v_diag_2767_ = lean_ctor_get_uint8(v___y_2742_, sizeof(void*)*14);
v_cancelTk_x3f_2768_ = lean_ctor_get(v___y_2742_, 12);
v_suppressElabErrors_2769_ = lean_ctor_get_uint8(v___y_2742_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2770_ = lean_ctor_get(v___y_2742_, 13);
v___x_2778_ = lean_unsigned_to_nat(0u);
v___x_2779_ = lean_nat_dec_eq(v_maxRecDepth_2759_, v___x_2778_);
v___x_2780_ = lean_bool_not(v___x_2779_);
if (v___x_2780_ == 0)
{
v___y_2772_ = v___x_2780_;
goto v___jp_2771_;
}
else
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_eq(v_currRecDepth_2758_, v_maxRecDepth_2759_);
v___y_2772_ = v___x_2781_;
goto v___jp_2771_;
}
v___jp_2745_:
{
if (lean_obj_tag(v___y_2746_) == 0)
{
return v___y_2746_;
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_a_2747_ = lean_ctor_get(v___y_2746_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___y_2746_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___y_2746_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___y_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
v___jp_2771_:
{
if (v___y_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2773_ = lean_unsigned_to_nat(1u);
v___x_2774_ = lean_nat_add(v_currRecDepth_2758_, v___x_2773_);
lean_inc_ref(v_inheritedTraceOptions_2770_);
lean_inc(v_cancelTk_x3f_2768_);
lean_inc(v_currMacroScope_2766_);
lean_inc(v_quotContext_2765_);
lean_inc(v_maxHeartbeats_2764_);
lean_inc(v_initHeartbeats_2763_);
lean_inc(v_openDecls_2762_);
lean_inc(v_currNamespace_2761_);
lean_inc(v_ref_2760_);
lean_inc(v_maxRecDepth_2759_);
lean_inc_ref(v_options_2757_);
lean_inc_ref(v_fileMap_2756_);
lean_inc_ref(v_fileName_2755_);
v___x_2775_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2775_, 0, v_fileName_2755_);
lean_ctor_set(v___x_2775_, 1, v_fileMap_2756_);
lean_ctor_set(v___x_2775_, 2, v_options_2757_);
lean_ctor_set(v___x_2775_, 3, v___x_2774_);
lean_ctor_set(v___x_2775_, 4, v_maxRecDepth_2759_);
lean_ctor_set(v___x_2775_, 5, v_ref_2760_);
lean_ctor_set(v___x_2775_, 6, v_currNamespace_2761_);
lean_ctor_set(v___x_2775_, 7, v_openDecls_2762_);
lean_ctor_set(v___x_2775_, 8, v_initHeartbeats_2763_);
lean_ctor_set(v___x_2775_, 9, v_maxHeartbeats_2764_);
lean_ctor_set(v___x_2775_, 10, v_quotContext_2765_);
lean_ctor_set(v___x_2775_, 11, v_currMacroScope_2766_);
lean_ctor_set(v___x_2775_, 12, v_cancelTk_x3f_2768_);
lean_ctor_set(v___x_2775_, 13, v_inheritedTraceOptions_2770_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*14, v_diag_2767_);
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*14 + 1, v_suppressElabErrors_2769_);
lean_inc(v___y_2743_);
lean_inc(v___y_2741_);
lean_inc_ref(v___y_2740_);
lean_inc(v___y_2739_);
v___x_2776_ = lean_apply_6(v_x_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___x_2775_, v___y_2743_, lean_box(0));
v___y_2746_ = v___x_2776_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2777_; 
lean_dec_ref(v_x_2738_);
lean_inc(v_ref_2760_);
v___x_2777_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2760_);
v___y_2746_ = v___x_2777_;
goto v___jp_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2793_, lean_object* v_pre_2794_, lean_object* v_post_2795_, uint8_t v_usedLetOnly_2796_, uint8_t v_skipConstInApp_2797_, uint8_t v_skipInstances_2798_, lean_object* v_body_2799_, lean_object* v_x_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = lean_array_push(v_fvars_2793_, v_x_2800_);
v___x_2808_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2794_, v_post_2795_, v_usedLetOnly_2796_, v_skipConstInApp_2797_, v_skipInstances_2798_, v___x_2807_, v_body_2799_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2809_, lean_object* v_pre_2810_, lean_object* v_post_2811_, lean_object* v_usedLetOnly_2812_, lean_object* v_skipConstInApp_2813_, lean_object* v_skipInstances_2814_, lean_object* v_body_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_usedLetOnly_boxed_2823_; uint8_t v_skipConstInApp_boxed_2824_; uint8_t v_skipInstances_boxed_2825_; lean_object* v_res_2826_; 
v_usedLetOnly_boxed_2823_ = lean_unbox(v_usedLetOnly_2812_);
v_skipConstInApp_boxed_2824_ = lean_unbox(v_skipConstInApp_2813_);
v_skipInstances_boxed_2825_ = lean_unbox(v_skipInstances_2814_);
v_res_2826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2809_, v_pre_2810_, v_post_2811_, v_usedLetOnly_boxed_2823_, v_skipConstInApp_boxed_2824_, v_skipInstances_boxed_2825_, v_body_2815_, v_x_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2827_, lean_object* v_post_2828_, uint8_t v_usedLetOnly_2829_, uint8_t v_skipConstInApp_2830_, uint8_t v_skipInstances_2831_, lean_object* v_e_2832_, lean_object* v_a_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; 
lean_inc_ref(v_post_2828_);
lean_inc(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc_ref(v_e_2832_);
v___x_2839_ = lean_apply_6(v_post_2828_, v_e_2832_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, lean_box(0));
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2858_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2858_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2858_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
switch(lean_obj_tag(v_a_2840_))
{
case 0:
{
lean_object* v_e_2844_; lean_object* v___x_2846_; 
lean_dec_ref(v_e_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_e_2844_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_ref(v_e_2844_);
lean_dec_ref_known(v_a_2840_, 1);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_e_2844_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_e_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
case 1:
{
lean_object* v_e_2848_; lean_object* v___x_2849_; 
lean_del_object(v___x_2842_);
lean_dec_ref(v_e_2832_);
v_e_2848_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_ref(v_e_2848_);
lean_dec_ref_known(v_a_2840_, 1);
v___x_2849_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2827_, v_post_2828_, v_usedLetOnly_2829_, v_skipConstInApp_2830_, v_skipInstances_2831_, v_e_2848_, v_a_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2849_;
}
default: 
{
lean_object* v_e_x3f_2850_; 
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_e_x3f_2850_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_e_x3f_2850_);
lean_dec_ref_known(v_a_2840_, 1);
if (lean_obj_tag(v_e_x3f_2850_) == 0)
{
lean_object* v___x_2852_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_e_2832_);
v___x_2852_ = v___x_2842_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_e_2832_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2856_; 
lean_dec_ref(v_e_2832_);
v_val_2854_ = lean_ctor_get(v_e_x3f_2850_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v_e_x3f_2850_, 1);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v_val_2854_);
v___x_2856_ = v___x_2842_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_val_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v_e_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_a_2859_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2839_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2839_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2867_, lean_object* v_post_2868_, uint8_t v_usedLetOnly_2869_, uint8_t v_skipConstInApp_2870_, uint8_t v_skipInstances_2871_, lean_object* v_fvars_2872_, lean_object* v_e_2873_, lean_object* v_a_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
if (lean_obj_tag(v_e_2873_) == 6)
{
lean_object* v_binderName_2880_; lean_object* v_binderType_2881_; lean_object* v_body_2882_; uint8_t v_binderInfo_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_binderName_2880_ = lean_ctor_get(v_e_2873_, 0);
lean_inc(v_binderName_2880_);
v_binderType_2881_ = lean_ctor_get(v_e_2873_, 1);
lean_inc_ref(v_binderType_2881_);
v_body_2882_ = lean_ctor_get(v_e_2873_, 2);
lean_inc_ref(v_body_2882_);
v_binderInfo_2883_ = lean_ctor_get_uint8(v_e_2873_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2873_, 3);
v___x_2884_ = lean_expr_instantiate_rev(v_binderType_2881_, v_fvars_2872_);
lean_dec_ref(v_binderType_2881_);
lean_inc_ref(v_post_2868_);
lean_inc_ref(v_pre_2867_);
v___x_2885_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2867_, v_post_2868_, v_usedLetOnly_2869_, v_skipConstInApp_2870_, v_skipInstances_2871_, v___x_2884_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___f_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = lean_box(v_usedLetOnly_2869_);
v___x_2888_ = lean_box(v_skipConstInApp_2870_);
v___x_2889_ = lean_box(v_skipInstances_2871_);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2890_, 0, v_fvars_2872_);
lean_closure_set(v___f_2890_, 1, v_pre_2867_);
lean_closure_set(v___f_2890_, 2, v_post_2868_);
lean_closure_set(v___f_2890_, 3, v___x_2887_);
lean_closure_set(v___f_2890_, 4, v___x_2888_);
lean_closure_set(v___f_2890_, 5, v___x_2889_);
lean_closure_set(v___f_2890_, 6, v_body_2882_);
v___x_2891_ = 0;
v___x_2892_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2880_, v_binderInfo_2883_, v_a_2886_, v___f_2890_, v___x_2891_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2892_;
}
else
{
lean_dec_ref(v_body_2882_);
lean_dec(v_binderName_2880_);
lean_dec_ref(v_fvars_2872_);
lean_dec_ref(v_post_2868_);
lean_dec_ref(v_pre_2867_);
return v___x_2885_;
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_expr_instantiate_rev(v_e_2873_, v_fvars_2872_);
lean_dec_ref(v_e_2873_);
lean_inc_ref(v_post_2868_);
lean_inc_ref(v_pre_2867_);
v___x_2894_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2867_, v_post_2868_, v_usedLetOnly_2869_, v_skipConstInApp_2870_, v_skipInstances_2871_, v___x_2893_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; uint8_t v___x_2896_; uint8_t v___x_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = 0;
v___x_2897_ = 1;
v___x_2898_ = 1;
v___x_2899_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2872_, v_a_2895_, v___x_2896_, v_usedLetOnly_2869_, v___x_2896_, v___x_2897_, v___x_2898_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec_ref(v_fvars_2872_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2867_, v_post_2868_, v_usedLetOnly_2869_, v_skipConstInApp_2870_, v_skipInstances_2871_, v_a_2900_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2901_;
}
else
{
lean_dec_ref(v_post_2868_);
lean_dec_ref(v_pre_2867_);
return v___x_2899_;
}
}
else
{
lean_dec_ref(v_fvars_2872_);
lean_dec_ref(v_post_2868_);
lean_dec_ref(v_pre_2867_);
return v___x_2894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2902_, lean_object* v_pre_2903_, lean_object* v_post_2904_, uint8_t v_usedLetOnly_2905_, uint8_t v_skipConstInApp_2906_, uint8_t v_skipInstances_2907_, lean_object* v_body_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_array_push(v_fvars_2902_, v_x_2909_);
v___x_2917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2903_, v_post_2904_, v_usedLetOnly_2905_, v_skipConstInApp_2906_, v_skipInstances_2907_, v___x_2916_, v_body_2908_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2918_, lean_object* v_pre_2919_, lean_object* v_post_2920_, lean_object* v_usedLetOnly_2921_, lean_object* v_skipConstInApp_2922_, lean_object* v_skipInstances_2923_, lean_object* v_body_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
uint8_t v_usedLetOnly_boxed_2932_; uint8_t v_skipConstInApp_boxed_2933_; uint8_t v_skipInstances_boxed_2934_; lean_object* v_res_2935_; 
v_usedLetOnly_boxed_2932_ = lean_unbox(v_usedLetOnly_2921_);
v_skipConstInApp_boxed_2933_ = lean_unbox(v_skipConstInApp_2922_);
v_skipInstances_boxed_2934_ = lean_unbox(v_skipInstances_2923_);
v_res_2935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2918_, v_pre_2919_, v_post_2920_, v_usedLetOnly_boxed_2932_, v_skipConstInApp_boxed_2933_, v_skipInstances_boxed_2934_, v_body_2924_, v_x_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2936_, lean_object* v_post_2937_, uint8_t v_usedLetOnly_2938_, uint8_t v_skipConstInApp_2939_, uint8_t v_skipInstances_2940_, lean_object* v_fvars_2941_, lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
if (lean_obj_tag(v_e_2942_) == 8)
{
lean_object* v_declName_2949_; lean_object* v_type_2950_; lean_object* v_value_2951_; lean_object* v_body_2952_; uint8_t v_nondep_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_declName_2949_ = lean_ctor_get(v_e_2942_, 0);
lean_inc(v_declName_2949_);
v_type_2950_ = lean_ctor_get(v_e_2942_, 1);
lean_inc_ref(v_type_2950_);
v_value_2951_ = lean_ctor_get(v_e_2942_, 2);
lean_inc_ref(v_value_2951_);
v_body_2952_ = lean_ctor_get(v_e_2942_, 3);
lean_inc_ref(v_body_2952_);
v_nondep_2953_ = lean_ctor_get_uint8(v_e_2942_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2942_, 4);
v___x_2954_ = lean_expr_instantiate_rev(v_type_2950_, v_fvars_2941_);
lean_dec_ref(v_type_2950_);
lean_inc_ref(v_post_2937_);
lean_inc_ref(v_pre_2936_);
v___x_2955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v___x_2954_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = lean_expr_instantiate_rev(v_value_2951_, v_fvars_2941_);
lean_dec_ref(v_value_2951_);
lean_inc_ref(v_post_2937_);
lean_inc_ref(v_pre_2936_);
v___x_2958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v___x_2957_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___f_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = lean_box(v_usedLetOnly_2938_);
v___x_2961_ = lean_box(v_skipConstInApp_2939_);
v___x_2962_ = lean_box(v_skipInstances_2940_);
v___f_2963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2963_, 0, v_fvars_2941_);
lean_closure_set(v___f_2963_, 1, v_pre_2936_);
lean_closure_set(v___f_2963_, 2, v_post_2937_);
lean_closure_set(v___f_2963_, 3, v___x_2960_);
lean_closure_set(v___f_2963_, 4, v___x_2961_);
lean_closure_set(v___f_2963_, 5, v___x_2962_);
lean_closure_set(v___f_2963_, 6, v_body_2952_);
v___x_2964_ = 0;
v___x_2965_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2949_, v_a_2956_, v_a_2959_, v___f_2963_, v_nondep_2953_, v___x_2964_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
return v___x_2965_;
}
else
{
lean_dec(v_a_2956_);
lean_dec_ref(v_body_2952_);
lean_dec(v_declName_2949_);
lean_dec_ref(v_fvars_2941_);
lean_dec_ref(v_post_2937_);
lean_dec_ref(v_pre_2936_);
return v___x_2958_;
}
}
else
{
lean_dec_ref(v_body_2952_);
lean_dec_ref(v_value_2951_);
lean_dec(v_declName_2949_);
lean_dec_ref(v_fvars_2941_);
lean_dec_ref(v_post_2937_);
lean_dec_ref(v_pre_2936_);
return v___x_2955_;
}
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_expr_instantiate_rev(v_e_2942_, v_fvars_2941_);
lean_dec_ref(v_e_2942_);
lean_inc_ref(v_post_2937_);
lean_inc_ref(v_pre_2936_);
v___x_2967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v___x_2966_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; uint8_t v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = 0;
v___x_2970_ = 1;
v___x_2971_ = l_Lean_Meta_mkLetFVars(v_fvars_2941_, v_a_2968_, v_usedLetOnly_2938_, v___x_2969_, v___x_2970_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec_ref(v_fvars_2941_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v_a_2972_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
return v___x_2973_;
}
else
{
lean_dec_ref(v_post_2937_);
lean_dec_ref(v_pre_2936_);
return v___x_2971_;
}
}
else
{
lean_dec_ref(v_fvars_2941_);
lean_dec_ref(v_post_2937_);
lean_dec_ref(v_pre_2936_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2974_, lean_object* v_post_2975_, uint8_t v_usedLetOnly_2976_, uint8_t v_skipConstInApp_2977_, uint8_t v_skipInstances_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_bs_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v_post_2975_);
lean_dec_ref(v_pre_2974_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_bs_2981_);
return v___x_2989_;
}
else
{
lean_object* v_v_2990_; lean_object* v___x_2991_; 
v_v_2990_ = lean_array_uget_borrowed(v_bs_2981_, v_i_2980_);
lean_inc(v_v_2990_);
lean_inc_ref(v_post_2975_);
lean_inc_ref(v_pre_2974_);
v___x_2991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2974_, v_post_2975_, v_usedLetOnly_2976_, v_skipConstInApp_2977_, v_skipInstances_2978_, v_v_2990_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v_bs_x27_2994_; size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = lean_unsigned_to_nat(0u);
v_bs_x27_2994_ = lean_array_uset(v_bs_2981_, v_i_2980_, v___x_2993_);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2980_, v___x_2995_);
v___x_2997_ = lean_array_uset(v_bs_x27_2994_, v_i_2980_, v_a_2992_);
v_i_2980_ = v___x_2996_;
v_bs_2981_ = v___x_2997_;
goto _start;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_bs_2981_);
lean_dec_ref(v_post_2975_);
lean_dec_ref(v_pre_2974_);
v_a_2999_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2991_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2991_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3007_, lean_object* v_post_3008_, uint8_t v_usedLetOnly_3009_, uint8_t v_skipConstInApp_3010_, uint8_t v_skipInstances_3011_, lean_object* v___x_3012_, lean_object* v___y_3013_, lean_object* v_b_3014_, lean_object* v_a_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3007_, v_post_3008_, v_usedLetOnly_3009_, v_skipConstInApp_3010_, v_skipInstances_3011_, v___x_3012_, v___y_3013_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3031_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3031_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3031_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3026_ = lean_array_fset(v_b_3014_, v_a_3015_, v_a_3022_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_b_3014_);
v_a_3032_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3021_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3021_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3040_, lean_object* v_post_3041_, lean_object* v_usedLetOnly_3042_, lean_object* v_skipConstInApp_3043_, lean_object* v_skipInstances_3044_, lean_object* v___x_3045_, lean_object* v___y_3046_, lean_object* v_b_3047_, lean_object* v_a_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v_usedLetOnly_boxed_3054_; uint8_t v_skipConstInApp_boxed_3055_; uint8_t v_skipInstances_boxed_3056_; lean_object* v_res_3057_; 
v_usedLetOnly_boxed_3054_ = lean_unbox(v_usedLetOnly_3042_);
v_skipConstInApp_boxed_3055_ = lean_unbox(v_skipConstInApp_3043_);
v_skipInstances_boxed_3056_ = lean_unbox(v_skipInstances_3044_);
v_res_3057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3040_, v_post_3041_, v_usedLetOnly_boxed_3054_, v_skipConstInApp_boxed_3055_, v_skipInstances_boxed_3056_, v___x_3045_, v___y_3046_, v_b_3047_, v_a_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v_a_3048_);
lean_dec(v___y_3046_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3058_, lean_object* v___x_3059_, lean_object* v_pre_3060_, lean_object* v_post_3061_, uint8_t v_usedLetOnly_3062_, uint8_t v_skipConstInApp_3063_, uint8_t v_skipInstances_3064_, lean_object* v_a_3065_, lean_object* v_b_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___y_3074_; uint8_t v___x_3097_; 
v___x_3097_ = lean_nat_dec_lt(v_a_3065_, v_upperBound_3058_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; 
lean_dec(v_a_3065_);
lean_dec_ref(v_post_3061_);
lean_dec_ref(v_pre_3060_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_b_3066_);
return v___x_3098_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3099_ = lean_array_fget_borrowed(v_b_3066_, v_a_3065_);
v___x_3100_ = lean_array_get_size(v___x_3059_);
v___x_3101_ = lean_nat_dec_lt(v_a_3065_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; 
lean_inc(v___x_3099_);
v___x_3102_ = lean_box(v_usedLetOnly_3062_);
v___x_3103_ = lean_box(v_skipConstInApp_3063_);
v___x_3104_ = lean_box(v_skipInstances_3064_);
lean_inc(v_a_3065_);
lean_inc(v___y_3067_);
lean_inc_ref(v_post_3061_);
lean_inc_ref(v_pre_3060_);
v___f_3105_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3105_, 0, v_pre_3060_);
lean_closure_set(v___f_3105_, 1, v_post_3061_);
lean_closure_set(v___f_3105_, 2, v___x_3102_);
lean_closure_set(v___f_3105_, 3, v___x_3103_);
lean_closure_set(v___f_3105_, 4, v___x_3104_);
lean_closure_set(v___f_3105_, 5, v___x_3099_);
lean_closure_set(v___f_3105_, 6, v___y_3067_);
lean_closure_set(v___f_3105_, 7, v_b_3066_);
lean_closure_set(v___f_3105_, 8, v_a_3065_);
v___y_3074_ = v___f_3105_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3106_; uint8_t v_isInstance_3107_; 
v___x_3106_ = lean_array_fget_borrowed(v___x_3059_, v_a_3065_);
v_isInstance_3107_ = lean_ctor_get_uint8(v___x_3106_, sizeof(void*)*1 + 4);
if (v_isInstance_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___f_3111_; 
lean_inc(v___x_3099_);
v___x_3108_ = lean_box(v_usedLetOnly_3062_);
v___x_3109_ = lean_box(v_skipConstInApp_3063_);
v___x_3110_ = lean_box(v_skipInstances_3064_);
lean_inc(v_a_3065_);
lean_inc(v___y_3067_);
lean_inc_ref(v_post_3061_);
lean_inc_ref(v_pre_3060_);
v___f_3111_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3111_, 0, v_pre_3060_);
lean_closure_set(v___f_3111_, 1, v_post_3061_);
lean_closure_set(v___f_3111_, 2, v___x_3108_);
lean_closure_set(v___f_3111_, 3, v___x_3109_);
lean_closure_set(v___f_3111_, 4, v___x_3110_);
lean_closure_set(v___f_3111_, 5, v___x_3099_);
lean_closure_set(v___f_3111_, 6, v___y_3067_);
lean_closure_set(v___f_3111_, 7, v_b_3066_);
lean_closure_set(v___f_3111_, 8, v_a_3065_);
v___y_3074_ = v___f_3111_;
goto v___jp_3073_;
}
else
{
lean_object* v___x_3112_; lean_object* v___f_3113_; 
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_b_3066_);
v___f_3113_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3113_, 0, v___x_3112_);
v___y_3074_ = v___f_3113_;
goto v___jp_3073_;
}
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; 
lean_inc(v___y_3071_);
lean_inc_ref(v___y_3070_);
lean_inc(v___y_3069_);
lean_inc_ref(v___y_3068_);
v___x_3075_ = lean_apply_5(v___y_3074_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, lean_box(0));
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3088_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3088_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3088_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
if (lean_obj_tag(v_a_3076_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3082_; 
lean_dec(v_a_3065_);
lean_dec_ref(v_post_3061_);
lean_dec_ref(v_pre_3060_);
v_a_3080_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v_a_3076_, 1);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v_a_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_del_object(v___x_3078_);
v_a_3084_ = lean_ctor_get(v_a_3076_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v_a_3076_, 1);
v___x_3085_ = lean_unsigned_to_nat(1u);
v___x_3086_ = lean_nat_add(v_a_3065_, v___x_3085_);
lean_dec(v_a_3065_);
v_a_3065_ = v___x_3086_;
v_b_3066_ = v_a_3084_;
goto _start;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3065_);
lean_dec_ref(v_post_3061_);
lean_dec_ref(v_pre_3060_);
v_a_3089_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3075_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3075_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3114_, lean_object* v_pre_3115_, lean_object* v_post_3116_, uint8_t v_usedLetOnly_3117_, uint8_t v_skipConstInApp_3118_, lean_object* v_x_3119_, lean_object* v_x_3120_, lean_object* v_x_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_f_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; 
if (lean_obj_tag(v_x_3119_) == 5)
{
lean_object* v_fn_3177_; lean_object* v_arg_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_fn_3177_ = lean_ctor_get(v_x_3119_, 0);
lean_inc_ref(v_fn_3177_);
v_arg_3178_ = lean_ctor_get(v_x_3119_, 1);
lean_inc_ref(v_arg_3178_);
lean_dec_ref_known(v_x_3119_, 2);
v___x_3179_ = lean_array_set(v_x_3120_, v_x_3121_, v_arg_3178_);
v___x_3180_ = lean_unsigned_to_nat(1u);
v___x_3181_ = lean_nat_sub(v_x_3121_, v___x_3180_);
lean_dec(v_x_3121_);
v_x_3119_ = v_fn_3177_;
v_x_3120_ = v___x_3179_;
v_x_3121_ = v___x_3181_;
goto _start;
}
else
{
lean_dec(v_x_3121_);
if (v_skipConstInApp_3118_ == 0)
{
goto v___jp_3174_;
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = l_Lean_Expr_isConst(v_x_3119_);
if (v___x_3183_ == 0)
{
goto v___jp_3174_;
}
else
{
v_f_3129_ = v_x_3119_;
v___y_3130_ = v___y_3122_;
v___y_3131_ = v___y_3123_;
v___y_3132_ = v___y_3124_;
v___y_3133_ = v___y_3125_;
v___y_3134_ = v___y_3126_;
goto v___jp_3128_;
}
}
}
v___jp_3128_:
{
if (v_skipInstances_3114_ == 0)
{
size_t v_sz_3135_; size_t v___x_3136_; lean_object* v___x_3137_; 
v_sz_3135_ = lean_array_size(v_x_3120_);
v___x_3136_ = ((size_t)0ULL);
lean_inc_ref(v_post_3116_);
lean_inc_ref(v_pre_3115_);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3114_, v_sz_3135_, v___x_3136_, v_x_3120_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = l_Lean_mkAppN(v_f_3129_, v_a_3138_);
lean_dec(v_a_3138_);
v___x_3140_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3114_, v___x_3139_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3140_;
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_f_3129_);
lean_dec_ref(v_post_3116_);
lean_dec_ref(v_pre_3115_);
v_a_3141_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3137_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3137_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_array_get_size(v_x_3120_);
lean_inc_ref(v_f_3129_);
v___x_3150_ = l_Lean_Meta_getFunInfoNArgs(v_f_3129_, v___x_3149_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v_paramInfo_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
lean_dec_ref_known(v___x_3150_, 1);
v_paramInfo_3152_ = lean_ctor_get(v_a_3151_, 0);
lean_inc_ref(v_paramInfo_3152_);
lean_dec(v_a_3151_);
v___x_3153_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3116_);
lean_inc_ref(v_pre_3115_);
v___x_3154_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3149_, v_paramInfo_3152_, v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3114_, v___x_3153_, v_x_3120_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec_ref(v_paramInfo_3152_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = l_Lean_mkAppN(v_f_3129_, v_a_3155_);
lean_dec(v_a_3155_);
v___x_3157_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3114_, v___x_3156_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
return v___x_3157_;
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref(v_f_3129_);
lean_dec_ref(v_post_3116_);
lean_dec_ref(v_pre_3115_);
v_a_3158_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3154_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3154_);
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
lean_dec_ref(v_f_3129_);
lean_dec_ref(v_x_3120_);
lean_dec_ref(v_post_3116_);
lean_dec_ref(v_pre_3115_);
v_a_3166_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3150_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3150_);
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
v___jp_3174_:
{
lean_object* v___x_3175_; 
lean_inc_ref(v_post_3116_);
lean_inc_ref(v_pre_3115_);
v___x_3175_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3115_, v_post_3116_, v_usedLetOnly_3117_, v_skipConstInApp_3118_, v_skipInstances_3114_, v_x_3119_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3175_, 1);
v_f_3129_ = v_a_3176_;
v___y_3130_ = v___y_3122_;
v___y_3131_ = v___y_3123_;
v___y_3132_ = v___y_3124_;
v___y_3133_ = v___y_3125_;
v___y_3134_ = v___y_3126_;
goto v___jp_3128_;
}
else
{
lean_dec_ref(v_x_3120_);
lean_dec_ref(v_post_3116_);
lean_dec_ref(v_pre_3115_);
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3184_, lean_object* v_pre_3185_, lean_object* v_e_3186_, lean_object* v_post_3187_, uint8_t v_usedLetOnly_3188_, uint8_t v_skipConstInApp_3189_, uint8_t v_skipInstances_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Core_checkSystem(v___x_3184_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v___x_3198_; 
lean_dec_ref_known(v___x_3197_, 1);
lean_inc_ref(v_pre_3185_);
lean_inc(v___y_3195_);
lean_inc_ref(v___y_3194_);
lean_inc(v___y_3193_);
lean_inc_ref(v___y_3192_);
lean_inc_ref(v_e_3186_);
v___x_3198_ = lean_apply_6(v_pre_3185_, v_e_3186_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, lean_box(0));
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3247_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3247_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3247_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___y_3204_; 
switch(lean_obj_tag(v_a_3199_))
{
case 0:
{
lean_object* v_e_3239_; lean_object* v___x_3241_; 
lean_dec_ref(v_post_3187_);
lean_dec_ref(v_e_3186_);
lean_dec_ref(v_pre_3185_);
v_e_3239_ = lean_ctor_get(v_a_3199_, 0);
lean_inc_ref(v_e_3239_);
lean_dec_ref_known(v_a_3199_, 1);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_e_3239_);
v___x_3241_ = v___x_3201_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_e_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
case 1:
{
lean_object* v_e_3243_; lean_object* v___x_3244_; 
lean_del_object(v___x_3201_);
lean_dec_ref(v_e_3186_);
v_e_3243_ = lean_ctor_get(v_a_3199_, 0);
lean_inc_ref(v_e_3243_);
lean_dec_ref_known(v_a_3199_, 1);
v___x_3244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v_e_3243_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3244_;
}
default: 
{
lean_object* v_e_x3f_3245_; 
lean_del_object(v___x_3201_);
v_e_x3f_3245_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_e_x3f_3245_);
lean_dec_ref_known(v_a_3199_, 1);
if (lean_obj_tag(v_e_x3f_3245_) == 0)
{
v___y_3204_ = v_e_3186_;
goto v___jp_3203_;
}
else
{
lean_object* v_val_3246_; 
lean_dec_ref(v_e_3186_);
v_val_3246_ = lean_ctor_get(v_e_x3f_3245_, 0);
lean_inc(v_val_3246_);
lean_dec_ref_known(v_e_x3f_3245_, 1);
v___y_3204_ = v_val_3246_;
goto v___jp_3203_;
}
}
}
v___jp_3203_:
{
switch(lean_obj_tag(v___y_3204_))
{
case 7:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___x_3205_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3206_;
}
case 6:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___x_3207_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3208_;
}
case 8:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___x_3209_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3210_;
}
case 5:
{
lean_object* v_dummy_3211_; lean_object* v_nargs_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_dummy_3211_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3212_ = l_Lean_Expr_getAppNumArgs(v___y_3204_);
lean_inc(v_nargs_3212_);
v___x_3213_ = lean_mk_array(v_nargs_3212_, v_dummy_3211_);
v___x_3214_ = lean_unsigned_to_nat(1u);
v___x_3215_ = lean_nat_sub(v_nargs_3212_, v___x_3214_);
lean_dec(v_nargs_3212_);
v___x_3216_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3190_, v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v___y_3204_, v___x_3213_, v___x_3215_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3216_;
}
case 10:
{
lean_object* v_data_3217_; lean_object* v_expr_3218_; lean_object* v___x_3219_; 
v_data_3217_ = lean_ctor_get(v___y_3204_, 0);
v_expr_3218_ = lean_ctor_get(v___y_3204_, 1);
lean_inc_ref(v_expr_3218_);
lean_inc_ref(v_post_3187_);
lean_inc_ref(v_pre_3185_);
v___x_3219_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v_expr_3218_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; size_t v___x_3221_; size_t v___x_3222_; uint8_t v___x_3223_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = lean_ptr_addr(v_expr_3218_);
v___x_3222_ = lean_ptr_addr(v_a_3220_);
v___x_3223_ = lean_usize_dec_eq(v___x_3221_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_inc(v_data_3217_);
lean_dec_ref_known(v___y_3204_, 2);
v___x_3224_ = l_Lean_Expr_mdata___override(v_data_3217_, v_a_3220_);
v___x_3225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___x_3224_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; 
lean_dec(v_a_3220_);
v___x_3226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3226_;
}
}
else
{
lean_dec_ref_known(v___y_3204_, 2);
lean_dec_ref(v_post_3187_);
lean_dec_ref(v_pre_3185_);
return v___x_3219_;
}
}
case 11:
{
lean_object* v_typeName_3227_; lean_object* v_idx_3228_; lean_object* v_struct_3229_; lean_object* v___x_3230_; 
v_typeName_3227_ = lean_ctor_get(v___y_3204_, 0);
v_idx_3228_ = lean_ctor_get(v___y_3204_, 1);
v_struct_3229_ = lean_ctor_get(v___y_3204_, 2);
lean_inc_ref(v_struct_3229_);
lean_inc_ref(v_post_3187_);
lean_inc_ref(v_pre_3185_);
v___x_3230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v_struct_3229_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; size_t v___x_3232_; size_t v___x_3233_; uint8_t v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = lean_ptr_addr(v_struct_3229_);
v___x_3233_ = lean_ptr_addr(v_a_3231_);
v___x_3234_ = lean_usize_dec_eq(v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_inc(v_idx_3228_);
lean_inc(v_typeName_3227_);
lean_dec_ref_known(v___y_3204_, 3);
v___x_3235_ = l_Lean_Expr_proj___override(v_typeName_3227_, v_idx_3228_, v_a_3231_);
v___x_3236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___x_3235_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; 
lean_dec(v_a_3231_);
v___x_3237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3237_;
}
}
else
{
lean_dec_ref_known(v___y_3204_, 3);
lean_dec_ref(v_post_3187_);
lean_dec_ref(v_pre_3185_);
return v___x_3230_;
}
}
default: 
{
lean_object* v___x_3238_; 
v___x_3238_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3185_, v_post_3187_, v_usedLetOnly_3188_, v_skipConstInApp_3189_, v_skipInstances_3190_, v___y_3204_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3238_;
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_post_3187_);
lean_dec_ref(v_e_3186_);
lean_dec_ref(v_pre_3185_);
v_a_3248_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3198_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3198_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v_post_3187_);
lean_dec_ref(v_e_3186_);
lean_dec_ref(v_pre_3185_);
v_a_3256_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3197_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3197_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3264_, lean_object* v_pre_3265_, lean_object* v_e_3266_, lean_object* v_post_3267_, lean_object* v_usedLetOnly_3268_, lean_object* v_skipConstInApp_3269_, lean_object* v_skipInstances_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
uint8_t v_usedLetOnly_boxed_3277_; uint8_t v_skipConstInApp_boxed_3278_; uint8_t v_skipInstances_boxed_3279_; lean_object* v_res_3280_; 
v_usedLetOnly_boxed_3277_ = lean_unbox(v_usedLetOnly_3268_);
v_skipConstInApp_boxed_3278_ = lean_unbox(v_skipConstInApp_3269_);
v_skipInstances_boxed_3279_ = lean_unbox(v_skipInstances_3270_);
v_res_3280_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3264_, v_pre_3265_, v_e_3266_, v_post_3267_, v_usedLetOnly_boxed_3277_, v_skipConstInApp_boxed_3278_, v_skipInstances_boxed_3279_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3281_, lean_object* v_post_3282_, uint8_t v_usedLetOnly_3283_, uint8_t v_skipConstInApp_3284_, uint8_t v_skipInstances_3285_, lean_object* v_e_3286_, lean_object* v_a_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc(v_a_3287_);
v___x_3293_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3293_, 0, lean_box(0));
lean_closure_set(v___x_3293_, 1, lean_box(0));
lean_closure_set(v___x_3293_, 2, v_a_3287_);
v___x_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3293_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3329_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3329_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3329_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3295_, v_e_3286_);
lean_dec(v_a_3295_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___f_3304_; lean_object* v___x_3305_; 
lean_del_object(v___x_3297_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3301_ = lean_box(v_usedLetOnly_3283_);
v___x_3302_ = lean_box(v_skipConstInApp_3284_);
v___x_3303_ = lean_box(v_skipInstances_3285_);
lean_inc_ref(v_e_3286_);
v___f_3304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3304_, 0, v___x_3300_);
lean_closure_set(v___f_3304_, 1, v_pre_3281_);
lean_closure_set(v___f_3304_, 2, v_e_3286_);
lean_closure_set(v___f_3304_, 3, v_post_3282_);
lean_closure_set(v___f_3304_, 4, v___x_3301_);
lean_closure_set(v___f_3304_, 5, v___x_3302_);
lean_closure_set(v___f_3304_, 6, v___x_3303_);
v___x_3305_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3304_, v_a_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc_n(v_a_3306_, 2);
lean_dec_ref_known(v___x_3305_, 1);
lean_inc(v_a_3287_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3307_, 0, v_a_3287_);
lean_closure_set(v___f_3307_, 1, v_e_3286_);
lean_closure_set(v___f_3307_, 2, v_a_3306_);
v___x_3308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3307_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v___x_3308_, 0);
lean_dec(v_unused_3316_);
v___x_3310_ = v___x_3308_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_dec(v___x_3308_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v_a_3306_);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3306_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_a_3306_);
v_a_3317_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3308_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3308_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_dec_ref(v_e_3286_);
return v___x_3305_;
}
}
else
{
lean_object* v_val_3325_; lean_object* v___x_3327_; 
lean_dec_ref(v_e_3286_);
lean_dec_ref(v_post_3282_);
lean_dec_ref(v_pre_3281_);
v_val_3325_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v___x_3299_, 1);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v_val_3325_);
v___x_3327_ = v___x_3297_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_val_3325_);
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
lean_dec_ref(v_e_3286_);
lean_dec_ref(v_post_3282_);
lean_dec_ref(v_pre_3281_);
v_a_3330_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3294_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3294_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3338_, lean_object* v_pre_3339_, lean_object* v_post_3340_, lean_object* v_usedLetOnly_3341_, lean_object* v_skipConstInApp_3342_, lean_object* v_skipInstances_3343_, lean_object* v_body_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v_usedLetOnly_boxed_3352_; uint8_t v_skipConstInApp_boxed_3353_; uint8_t v_skipInstances_boxed_3354_; lean_object* v_res_3355_; 
v_usedLetOnly_boxed_3352_ = lean_unbox(v_usedLetOnly_3341_);
v_skipConstInApp_boxed_3353_ = lean_unbox(v_skipConstInApp_3342_);
v_skipInstances_boxed_3354_ = lean_unbox(v_skipInstances_3343_);
v_res_3355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3338_, v_pre_3339_, v_post_3340_, v_usedLetOnly_boxed_3352_, v_skipConstInApp_boxed_3353_, v_skipInstances_boxed_3354_, v_body_3344_, v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3356_, lean_object* v_post_3357_, uint8_t v_usedLetOnly_3358_, uint8_t v_skipConstInApp_3359_, uint8_t v_skipInstances_3360_, lean_object* v_fvars_3361_, lean_object* v_e_3362_, lean_object* v_a_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
if (lean_obj_tag(v_e_3362_) == 7)
{
lean_object* v_binderName_3369_; lean_object* v_binderType_3370_; lean_object* v_body_3371_; uint8_t v_binderInfo_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_binderName_3369_ = lean_ctor_get(v_e_3362_, 0);
lean_inc(v_binderName_3369_);
v_binderType_3370_ = lean_ctor_get(v_e_3362_, 1);
lean_inc_ref(v_binderType_3370_);
v_body_3371_ = lean_ctor_get(v_e_3362_, 2);
lean_inc_ref(v_body_3371_);
v_binderInfo_3372_ = lean_ctor_get_uint8(v_e_3362_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3362_, 3);
v___x_3373_ = lean_expr_instantiate_rev(v_binderType_3370_, v_fvars_3361_);
lean_dec_ref(v_binderType_3370_);
lean_inc_ref(v_post_3357_);
lean_inc_ref(v_pre_3356_);
v___x_3374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v___x_3373_, v_a_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___f_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = lean_box(v_usedLetOnly_3358_);
v___x_3377_ = lean_box(v_skipConstInApp_3359_);
v___x_3378_ = lean_box(v_skipInstances_3360_);
v___f_3379_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3379_, 0, v_fvars_3361_);
lean_closure_set(v___f_3379_, 1, v_pre_3356_);
lean_closure_set(v___f_3379_, 2, v_post_3357_);
lean_closure_set(v___f_3379_, 3, v___x_3376_);
lean_closure_set(v___f_3379_, 4, v___x_3377_);
lean_closure_set(v___f_3379_, 5, v___x_3378_);
lean_closure_set(v___f_3379_, 6, v_body_3371_);
v___x_3380_ = 0;
v___x_3381_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3369_, v_binderInfo_3372_, v_a_3375_, v___f_3379_, v___x_3380_, v_a_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
return v___x_3381_;
}
else
{
lean_dec_ref(v_body_3371_);
lean_dec(v_binderName_3369_);
lean_dec_ref(v_fvars_3361_);
lean_dec_ref(v_post_3357_);
lean_dec_ref(v_pre_3356_);
return v___x_3374_;
}
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = lean_expr_instantiate_rev(v_e_3362_, v_fvars_3361_);
lean_dec_ref(v_e_3362_);
lean_inc_ref(v_post_3357_);
lean_inc_ref(v_pre_3356_);
v___x_3383_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v___x_3382_, v_a_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; uint8_t v___x_3385_; uint8_t v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = 0;
v___x_3386_ = 1;
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Meta_mkForallFVars(v_fvars_3361_, v_a_3384_, v___x_3385_, v_usedLetOnly_3358_, v___x_3386_, v___x_3387_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref(v_fvars_3361_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v_a_3389_, v_a_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
return v___x_3390_;
}
else
{
lean_dec_ref(v_post_3357_);
lean_dec_ref(v_pre_3356_);
return v___x_3388_;
}
}
else
{
lean_dec_ref(v_fvars_3361_);
lean_dec_ref(v_post_3357_);
lean_dec_ref(v_pre_3356_);
return v___x_3383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3391_, lean_object* v_pre_3392_, lean_object* v_post_3393_, uint8_t v_usedLetOnly_3394_, uint8_t v_skipConstInApp_3395_, uint8_t v_skipInstances_3396_, lean_object* v_body_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = lean_array_push(v_fvars_3391_, v_x_3398_);
v___x_3406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3392_, v_post_3393_, v_usedLetOnly_3394_, v_skipConstInApp_3395_, v_skipInstances_3396_, v___x_3405_, v_body_3397_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3407_, lean_object* v_post_3408_, lean_object* v_usedLetOnly_3409_, lean_object* v_skipConstInApp_3410_, lean_object* v_skipInstances_3411_, lean_object* v_e_3412_, lean_object* v_a_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v_usedLetOnly_boxed_3419_; uint8_t v_skipConstInApp_boxed_3420_; uint8_t v_skipInstances_boxed_3421_; lean_object* v_res_3422_; 
v_usedLetOnly_boxed_3419_ = lean_unbox(v_usedLetOnly_3409_);
v_skipConstInApp_boxed_3420_ = lean_unbox(v_skipConstInApp_3410_);
v_skipInstances_boxed_3421_ = lean_unbox(v_skipInstances_3411_);
v_res_3422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3407_, v_post_3408_, v_usedLetOnly_boxed_3419_, v_skipConstInApp_boxed_3420_, v_skipInstances_boxed_3421_, v_e_3412_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v_a_3413_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3423_, lean_object* v_post_3424_, lean_object* v_usedLetOnly_3425_, lean_object* v_skipConstInApp_3426_, lean_object* v_skipInstances_3427_, lean_object* v_sz_3428_, lean_object* v_i_3429_, lean_object* v_bs_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v_usedLetOnly_boxed_3437_; uint8_t v_skipConstInApp_boxed_3438_; uint8_t v_skipInstances_boxed_3439_; size_t v_sz_boxed_3440_; size_t v_i_boxed_3441_; lean_object* v_res_3442_; 
v_usedLetOnly_boxed_3437_ = lean_unbox(v_usedLetOnly_3425_);
v_skipConstInApp_boxed_3438_ = lean_unbox(v_skipConstInApp_3426_);
v_skipInstances_boxed_3439_ = lean_unbox(v_skipInstances_3427_);
v_sz_boxed_3440_ = lean_unbox_usize(v_sz_3428_);
lean_dec(v_sz_3428_);
v_i_boxed_3441_ = lean_unbox_usize(v_i_3429_);
lean_dec(v_i_3429_);
v_res_3442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3423_, v_post_3424_, v_usedLetOnly_boxed_3437_, v_skipConstInApp_boxed_3438_, v_skipInstances_boxed_3439_, v_sz_boxed_3440_, v_i_boxed_3441_, v_bs_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3443_, lean_object* v_post_3444_, lean_object* v_usedLetOnly_3445_, lean_object* v_skipConstInApp_3446_, lean_object* v_skipInstances_3447_, lean_object* v_e_3448_, lean_object* v_a_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_usedLetOnly_boxed_3455_; uint8_t v_skipConstInApp_boxed_3456_; uint8_t v_skipInstances_boxed_3457_; lean_object* v_res_3458_; 
v_usedLetOnly_boxed_3455_ = lean_unbox(v_usedLetOnly_3445_);
v_skipConstInApp_boxed_3456_ = lean_unbox(v_skipConstInApp_3446_);
v_skipInstances_boxed_3457_ = lean_unbox(v_skipInstances_3447_);
v_res_3458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3443_, v_post_3444_, v_usedLetOnly_boxed_3455_, v_skipConstInApp_boxed_3456_, v_skipInstances_boxed_3457_, v_e_3448_, v_a_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v_a_3449_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3459_, lean_object* v_post_3460_, lean_object* v_usedLetOnly_3461_, lean_object* v_skipConstInApp_3462_, lean_object* v_skipInstances_3463_, lean_object* v_fvars_3464_, lean_object* v_e_3465_, lean_object* v_a_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
uint8_t v_usedLetOnly_boxed_3472_; uint8_t v_skipConstInApp_boxed_3473_; uint8_t v_skipInstances_boxed_3474_; lean_object* v_res_3475_; 
v_usedLetOnly_boxed_3472_ = lean_unbox(v_usedLetOnly_3461_);
v_skipConstInApp_boxed_3473_ = lean_unbox(v_skipConstInApp_3462_);
v_skipInstances_boxed_3474_ = lean_unbox(v_skipInstances_3463_);
v_res_3475_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3459_, v_post_3460_, v_usedLetOnly_boxed_3472_, v_skipConstInApp_boxed_3473_, v_skipInstances_boxed_3474_, v_fvars_3464_, v_e_3465_, v_a_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v_a_3466_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3476_, lean_object* v_post_3477_, lean_object* v_usedLetOnly_3478_, lean_object* v_skipConstInApp_3479_, lean_object* v_skipInstances_3480_, lean_object* v_fvars_3481_, lean_object* v_e_3482_, lean_object* v_a_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
uint8_t v_usedLetOnly_boxed_3489_; uint8_t v_skipConstInApp_boxed_3490_; uint8_t v_skipInstances_boxed_3491_; lean_object* v_res_3492_; 
v_usedLetOnly_boxed_3489_ = lean_unbox(v_usedLetOnly_3478_);
v_skipConstInApp_boxed_3490_ = lean_unbox(v_skipConstInApp_3479_);
v_skipInstances_boxed_3491_ = lean_unbox(v_skipInstances_3480_);
v_res_3492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3476_, v_post_3477_, v_usedLetOnly_boxed_3489_, v_skipConstInApp_boxed_3490_, v_skipInstances_boxed_3491_, v_fvars_3481_, v_e_3482_, v_a_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v_a_3483_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3493_, lean_object* v_post_3494_, lean_object* v_usedLetOnly_3495_, lean_object* v_skipConstInApp_3496_, lean_object* v_skipInstances_3497_, lean_object* v_fvars_3498_, lean_object* v_e_3499_, lean_object* v_a_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
uint8_t v_usedLetOnly_boxed_3506_; uint8_t v_skipConstInApp_boxed_3507_; uint8_t v_skipInstances_boxed_3508_; lean_object* v_res_3509_; 
v_usedLetOnly_boxed_3506_ = lean_unbox(v_usedLetOnly_3495_);
v_skipConstInApp_boxed_3507_ = lean_unbox(v_skipConstInApp_3496_);
v_skipInstances_boxed_3508_ = lean_unbox(v_skipInstances_3497_);
v_res_3509_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3493_, v_post_3494_, v_usedLetOnly_boxed_3506_, v_skipConstInApp_boxed_3507_, v_skipInstances_boxed_3508_, v_fvars_3498_, v_e_3499_, v_a_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v_a_3500_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3510_, lean_object* v___x_3511_, lean_object* v_pre_3512_, lean_object* v_post_3513_, lean_object* v_usedLetOnly_3514_, lean_object* v_skipConstInApp_3515_, lean_object* v_skipInstances_3516_, lean_object* v_a_3517_, lean_object* v_b_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
uint8_t v_usedLetOnly_boxed_3525_; uint8_t v_skipConstInApp_boxed_3526_; uint8_t v_skipInstances_boxed_3527_; lean_object* v_res_3528_; 
v_usedLetOnly_boxed_3525_ = lean_unbox(v_usedLetOnly_3514_);
v_skipConstInApp_boxed_3526_ = lean_unbox(v_skipConstInApp_3515_);
v_skipInstances_boxed_3527_ = lean_unbox(v_skipInstances_3516_);
v_res_3528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3510_, v___x_3511_, v_pre_3512_, v_post_3513_, v_usedLetOnly_boxed_3525_, v_skipConstInApp_boxed_3526_, v_skipInstances_boxed_3527_, v_a_3517_, v_b_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___x_3511_);
lean_dec(v_upperBound_3510_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3529_, lean_object* v_pre_3530_, lean_object* v_post_3531_, lean_object* v_usedLetOnly_3532_, lean_object* v_skipConstInApp_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_, lean_object* v_x_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
uint8_t v_skipInstances_boxed_3543_; uint8_t v_usedLetOnly_boxed_3544_; uint8_t v_skipConstInApp_boxed_3545_; lean_object* v_res_3546_; 
v_skipInstances_boxed_3543_ = lean_unbox(v_skipInstances_3529_);
v_usedLetOnly_boxed_3544_ = lean_unbox(v_usedLetOnly_3532_);
v_skipConstInApp_boxed_3545_ = lean_unbox(v_skipConstInApp_3533_);
v_res_3546_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3543_, v_pre_3530_, v_post_3531_, v_usedLetOnly_boxed_3544_, v_skipConstInApp_boxed_3545_, v_x_3534_, v_x_3535_, v_x_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
return v_res_3546_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_unsigned_to_nat(16u);
v___x_3549_ = lean_mk_array(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3554_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3554_, 0, lean_box(0));
lean_closure_set(v___x_3554_, 1, lean_box(0));
lean_closure_set(v___x_3554_, 2, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3555_, lean_object* v_pre_3556_, lean_object* v_post_3557_, uint8_t v_usedLetOnly_3558_, uint8_t v_skipConstInApp_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_a_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3565_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3566_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3565_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = 0;
v___x_3569_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3556_, v_post_3557_, v_usedLetOnly_3558_, v_skipConstInApp_3559_, v___x_3568_, v_input_3555_, v_a_3567_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
v___x_3571_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3571_, 0, lean_box(0));
lean_closure_set(v___x_3571_, 1, lean_box(0));
lean_closure_set(v___x_3571_, 2, v_a_3567_);
v___x_3572_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3571_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3580_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_a_3570_);
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3570_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
else
{
lean_dec(v_a_3567_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3581_, lean_object* v_pre_3582_, lean_object* v_post_3583_, lean_object* v_usedLetOnly_3584_, lean_object* v_skipConstInApp_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v_usedLetOnly_boxed_3591_; uint8_t v_skipConstInApp_boxed_3592_; lean_object* v_res_3593_; 
v_usedLetOnly_boxed_3591_ = lean_unbox(v_usedLetOnly_3584_);
v_skipConstInApp_boxed_3592_ = lean_unbox(v_skipConstInApp_3585_);
v_res_3593_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3581_, v_pre_3582_, v_post_3583_, v_usedLetOnly_boxed_3591_, v_skipConstInApp_boxed_3592_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3595_, lean_object* v_p_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v_a_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; 
v___x_3602_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3595_, v_a_3598_);
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref(v___x_3602_);
v___f_3604_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3605_, 0, v_p_3596_);
v___x_3606_ = 0;
v___x_3607_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3603_, v___f_3604_, v___f_3605_, v___x_3606_, v___x_3606_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3608_, lean_object* v_p_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_etaStructReduce(v_e_3608_, v_p_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3616_, lean_object* v___x_3617_, lean_object* v_pre_3618_, lean_object* v_post_3619_, uint8_t v_usedLetOnly_3620_, uint8_t v_skipConstInApp_3621_, uint8_t v_skipInstances_3622_, lean_object* v___x_3623_, lean_object* v_inst_3624_, lean_object* v_R_3625_, lean_object* v_a_3626_, lean_object* v_b_3627_, lean_object* v_c_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3616_, v___x_3617_, v_pre_3618_, v_post_3619_, v_usedLetOnly_3620_, v_skipConstInApp_3621_, v_skipInstances_3622_, v_a_3626_, v_b_3627_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3636_ = _args[0];
lean_object* v___x_3637_ = _args[1];
lean_object* v_pre_3638_ = _args[2];
lean_object* v_post_3639_ = _args[3];
lean_object* v_usedLetOnly_3640_ = _args[4];
lean_object* v_skipConstInApp_3641_ = _args[5];
lean_object* v_skipInstances_3642_ = _args[6];
lean_object* v___x_3643_ = _args[7];
lean_object* v_inst_3644_ = _args[8];
lean_object* v_R_3645_ = _args[9];
lean_object* v_a_3646_ = _args[10];
lean_object* v_b_3647_ = _args[11];
lean_object* v_c_3648_ = _args[12];
lean_object* v___y_3649_ = _args[13];
lean_object* v___y_3650_ = _args[14];
lean_object* v___y_3651_ = _args[15];
lean_object* v___y_3652_ = _args[16];
lean_object* v___y_3653_ = _args[17];
lean_object* v___y_3654_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3655_; uint8_t v_skipConstInApp_boxed_3656_; uint8_t v_skipInstances_boxed_3657_; lean_object* v_res_3658_; 
v_usedLetOnly_boxed_3655_ = lean_unbox(v_usedLetOnly_3640_);
v_skipConstInApp_boxed_3656_ = lean_unbox(v_skipConstInApp_3641_);
v_skipInstances_boxed_3657_ = lean_unbox(v_skipInstances_3642_);
v_res_3658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3636_, v___x_3637_, v_pre_3638_, v_post_3639_, v_usedLetOnly_boxed_3655_, v_skipConstInApp_boxed_3656_, v_skipInstances_boxed_3657_, v___x_3643_, v_inst_3644_, v_R_3645_, v_a_3646_, v_b_3647_, v_c_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec(v___x_3643_);
lean_dec_ref(v___x_3637_);
lean_dec(v_upperBound_3636_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3659_, lean_object* v_m_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3660_, v_a_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3663_, lean_object* v_m_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3663_, v_m_3664_, v_a_3665_);
lean_dec_ref(v_a_3665_);
lean_dec_ref(v_m_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3667_, lean_object* v_name_3668_, uint8_t v_bi_3669_, lean_object* v_type_3670_, lean_object* v_k_3671_, uint8_t v_kind_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3668_, v_bi_3669_, v_type_3670_, v_k_3671_, v_kind_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_name_3681_, lean_object* v_bi_3682_, lean_object* v_type_3683_, lean_object* v_k_3684_, lean_object* v_kind_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_bi_boxed_3692_; uint8_t v_kind_boxed_3693_; lean_object* v_res_3694_; 
v_bi_boxed_3692_ = lean_unbox(v_bi_3682_);
v_kind_boxed_3693_ = lean_unbox(v_kind_3685_);
v_res_3694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3680_, v_name_3681_, v_bi_boxed_3692_, v_type_3683_, v_k_3684_, v_kind_boxed_3693_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3695_, lean_object* v_name_3696_, lean_object* v_type_3697_, lean_object* v_val_3698_, lean_object* v_k_3699_, uint8_t v_nondep_3700_, uint8_t v_kind_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3696_, v_type_3697_, v_val_3698_, v_k_3699_, v_nondep_3700_, v_kind_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3709_, lean_object* v_name_3710_, lean_object* v_type_3711_, lean_object* v_val_3712_, lean_object* v_k_3713_, lean_object* v_nondep_3714_, lean_object* v_kind_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
uint8_t v_nondep_boxed_3722_; uint8_t v_kind_boxed_3723_; lean_object* v_res_3724_; 
v_nondep_boxed_3722_ = lean_unbox(v_nondep_3714_);
v_kind_boxed_3723_ = lean_unbox(v_kind_3715_);
v_res_3724_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3709_, v_name_3710_, v_type_3711_, v_val_3712_, v_k_3713_, v_nondep_boxed_3722_, v_kind_boxed_3723_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3725_, lean_object* v_ref_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3726_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3733_, lean_object* v_ref_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3733_, v_ref_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3741_, lean_object* v_x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3750_, lean_object* v_x_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3750_, v_x_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3759_, lean_object* v_m_3760_, lean_object* v_a_3761_, lean_object* v_b_3762_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3760_, v_a_3761_, v_b_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3764_, lean_object* v_a_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3765_, v_x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3768_, lean_object* v_a_3769_, lean_object* v_x_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3768_, v_a_3769_, v_x_3770_);
lean_dec(v_x_3770_);
lean_dec_ref(v_a_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3772_, lean_object* v_a_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v___x_3775_; 
v___x_3775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3773_, v_x_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3776_, lean_object* v_a_3777_, lean_object* v_x_3778_){
_start:
{
uint8_t v_res_3779_; lean_object* v_r_3780_; 
v_res_3779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3776_, v_a_3777_, v_x_3778_);
lean_dec(v_x_3778_);
lean_dec_ref(v_a_3777_);
v_r_3780_ = lean_box(v_res_3779_);
return v_r_3780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3781_, lean_object* v_data_3782_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3784_, lean_object* v_a_3785_, lean_object* v_b_3786_, lean_object* v_x_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3785_, v_b_3786_, v_x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3789_, lean_object* v_i_3790_, lean_object* v_source_3791_, lean_object* v_target_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3790_, v_source_3791_, v_target_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3794_, lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3795_, v_x_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3798_, lean_object* v_inst_3799_, lean_object* v_toBind_3800_, lean_object* v___f_3801_, lean_object* v_____do__lift_3802_){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3803_, 0, v_____do__lift_3802_);
lean_closure_set(v___x_3803_, 1, v_binderType_3798_);
v___x_3804_ = lean_apply_2(v_inst_3799_, lean_box(0), v___x_3803_);
v___x_3805_ = lean_apply_4(v_toBind_3800_, lean_box(0), lean_box(0), v___x_3804_, v___f_3801_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3806_, lean_object* v_usedFields_3807_, lean_object* v_binderName_3808_, lean_object* v_body_3809_, lean_object* v_val_3810_, lean_object* v_inst_3811_, lean_object* v_inst_3812_, lean_object* v_fieldVal_x3f_3813_, lean_object* v_____do__lift_3814_){
_start:
{
uint8_t v_____do__lift_469__boxed_3815_; lean_object* v_res_3816_; 
v_____do__lift_469__boxed_3815_ = lean_unbox(v_____do__lift_3814_);
v_res_3816_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3806_, v_usedFields_3807_, v_binderName_3808_, v_body_3809_, v_val_3810_, v_inst_3811_, v_inst_3812_, v_fieldVal_x3f_3813_, v_____do__lift_469__boxed_3815_);
lean_dec_ref(v_val_3810_);
lean_dec_ref(v_body_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3817_, lean_object* v_usedFields_3818_, lean_object* v_binderName_3819_, lean_object* v_body_3820_, lean_object* v_inst_3821_, lean_object* v_inst_3822_, lean_object* v_fieldVal_x3f_3823_, lean_object* v_binderType_3824_, lean_object* v_toBind_3825_, lean_object* v_____x_3826_){
_start:
{
if (lean_obj_tag(v_____x_3826_) == 1)
{
lean_object* v_val_3827_; lean_object* v___f_3828_; lean_object* v___f_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_val_3827_ = lean_ctor_get(v_____x_3826_, 0);
lean_inc_n(v_val_3827_, 2);
lean_dec_ref_known(v_____x_3826_, 1);
lean_inc_n(v_inst_3822_, 2);
v___f_3828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3828_, 0, v_toPure_3817_);
lean_closure_set(v___f_3828_, 1, v_usedFields_3818_);
lean_closure_set(v___f_3828_, 2, v_binderName_3819_);
lean_closure_set(v___f_3828_, 3, v_body_3820_);
lean_closure_set(v___f_3828_, 4, v_val_3827_);
lean_closure_set(v___f_3828_, 5, v_inst_3821_);
lean_closure_set(v___f_3828_, 6, v_inst_3822_);
lean_closure_set(v___f_3828_, 7, v_fieldVal_x3f_3823_);
lean_inc(v_toBind_3825_);
v___f_3829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3829_, 0, v_binderType_3824_);
lean_closure_set(v___f_3829_, 1, v_inst_3822_);
lean_closure_set(v___f_3829_, 2, v_toBind_3825_);
lean_closure_set(v___f_3829_, 3, v___f_3828_);
v___x_3830_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3830_, 0, v_val_3827_);
v___x_3831_ = lean_apply_2(v_inst_3822_, lean_box(0), v___x_3830_);
v___x_3832_ = lean_apply_4(v_toBind_3825_, lean_box(0), lean_box(0), v___x_3831_, v___f_3829_);
return v___x_3832_;
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec(v_____x_3826_);
lean_dec(v_toBind_3825_);
lean_dec_ref(v_binderType_3824_);
lean_dec(v_fieldVal_x3f_3823_);
lean_dec(v_inst_3822_);
lean_dec_ref(v_inst_3821_);
lean_dec_ref(v_body_3820_);
lean_dec(v_binderName_3819_);
lean_dec(v_usedFields_3818_);
v___x_3833_ = lean_box(0);
v___x_3834_ = lean_apply_2(v_toPure_3817_, lean_box(0), v___x_3833_);
return v___x_3834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3838_, lean_object* v_inst_3839_, lean_object* v_fieldVal_x3f_3840_, lean_object* v_usedFields_3841_, lean_object* v_e_3842_){
_start:
{
lean_object* v_toApplicative_3843_; lean_object* v_toBind_3844_; lean_object* v_toPure_3845_; 
v_toApplicative_3843_ = lean_ctor_get(v_inst_3838_, 0);
v_toBind_3844_ = lean_ctor_get(v_inst_3838_, 1);
v_toPure_3845_ = lean_ctor_get(v_toApplicative_3843_, 1);
lean_inc(v_toPure_3845_);
if (lean_obj_tag(v_e_3842_) == 6)
{
lean_object* v_binderName_3850_; lean_object* v_binderType_3851_; lean_object* v_body_3852_; lean_object* v___f_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_inc_n(v_toBind_3844_, 2);
v_binderName_3850_ = lean_ctor_get(v_e_3842_, 0);
lean_inc_n(v_binderName_3850_, 2);
v_binderType_3851_ = lean_ctor_get(v_e_3842_, 1);
lean_inc_ref(v_binderType_3851_);
v_body_3852_ = lean_ctor_get(v_e_3842_, 2);
lean_inc_ref(v_body_3852_);
lean_dec_ref_known(v_e_3842_, 3);
lean_inc(v_fieldVal_x3f_3840_);
v___f_3853_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3853_, 0, v_toPure_3845_);
lean_closure_set(v___f_3853_, 1, v_usedFields_3841_);
lean_closure_set(v___f_3853_, 2, v_binderName_3850_);
lean_closure_set(v___f_3853_, 3, v_body_3852_);
lean_closure_set(v___f_3853_, 4, v_inst_3838_);
lean_closure_set(v___f_3853_, 5, v_inst_3839_);
lean_closure_set(v___f_3853_, 6, v_fieldVal_x3f_3840_);
lean_closure_set(v___f_3853_, 7, v_binderType_3851_);
lean_closure_set(v___f_3853_, 8, v_toBind_3844_);
v___x_3854_ = lean_apply_1(v_fieldVal_x3f_3840_, v_binderName_3850_);
v___x_3855_ = lean_apply_4(v_toBind_3844_, lean_box(0), lean_box(0), v___x_3854_, v___f_3853_);
return v___x_3855_;
}
else
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3872_; 
lean_dec(v_fieldVal_x3f_3840_);
lean_dec(v_inst_3839_);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_inst_3838_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3873_ = lean_ctor_get(v_inst_3838_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_inst_3838_, 0);
lean_dec(v_unused_3874_);
v___x_3857_ = v_inst_3838_;
v_isShared_3858_ = v_isSharedCheck_3872_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_inst_3838_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3872_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
lean_inc_ref(v_e_3842_);
v___x_3859_ = l_Lean_Expr_cleanupAnnotations(v_e_3842_);
v___x_3860_ = l_Lean_Expr_isApp(v___x_3859_);
if (v___x_3860_ == 0)
{
lean_dec_ref(v___x_3859_);
lean_del_object(v___x_3857_);
goto v___jp_3846_;
}
else
{
lean_object* v_arg_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_arg_3861_ = lean_ctor_get(v___x_3859_, 1);
lean_inc_ref(v_arg_3861_);
v___x_3862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3859_);
v___x_3863_ = l_Lean_Expr_isApp(v___x_3862_);
if (v___x_3863_ == 0)
{
lean_dec_ref(v___x_3862_);
lean_dec_ref(v_arg_3861_);
lean_del_object(v___x_3857_);
goto v___jp_3846_;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3862_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3866_ = l_Lean_Expr_isConstOf(v___x_3864_, v___x_3865_);
lean_dec_ref(v___x_3864_);
if (v___x_3866_ == 0)
{
lean_dec_ref(v_arg_3861_);
lean_del_object(v___x_3857_);
goto v___jp_3846_;
}
else
{
lean_object* v___x_3868_; 
lean_dec_ref(v_e_3842_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 1, v_arg_3861_);
lean_ctor_set(v___x_3857_, 0, v_usedFields_3841_);
v___x_3868_ = v___x_3857_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_usedFields_3841_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_arg_3861_);
v___x_3868_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
v___x_3870_ = lean_apply_2(v_toPure_3845_, lean_box(0), v___x_3869_);
return v___x_3870_;
}
}
}
}
}
}
v___jp_3846_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_usedFields_3841_);
lean_ctor_set(v___x_3847_, 1, v_e_3842_);
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
v___x_3849_ = lean_apply_2(v_toPure_3845_, lean_box(0), v___x_3848_);
return v___x_3849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3875_, lean_object* v_usedFields_3876_, lean_object* v_binderName_3877_, lean_object* v_body_3878_, lean_object* v_val_3879_, lean_object* v_inst_3880_, lean_object* v_inst_3881_, lean_object* v_fieldVal_x3f_3882_, uint8_t v_____do__lift_3883_){
_start:
{
if (v_____do__lift_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_dec(v_fieldVal_x3f_3882_);
lean_dec(v_inst_3881_);
lean_dec_ref(v_inst_3880_);
lean_dec(v_binderName_3877_);
lean_dec(v_usedFields_3876_);
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_apply_2(v_toPure_3875_, lean_box(0), v___x_3884_);
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
lean_dec(v_toPure_3875_);
v___x_3886_ = l_Lean_NameSet_insert(v_usedFields_3876_, v_binderName_3877_);
v___x_3887_ = lean_expr_instantiate1(v_body_3878_, v_val_3879_);
v___x_3888_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3880_, v_inst_3881_, v_fieldVal_x3f_3882_, v___x_3886_, v___x_3887_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3889_, lean_object* v_inst_3890_, lean_object* v_inst_3891_, lean_object* v_fieldVal_x3f_3892_, lean_object* v_usedFields_3893_, lean_object* v_e_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3890_, v_inst_3891_, v_fieldVal_x3f_3892_, v_usedFields_3893_, v_e_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3896_, lean_object* v_inst_3897_, lean_object* v_fieldVal_x3f_3898_, lean_object* v_toPure_3899_, lean_object* v_____s_3900_){
_start:
{
lean_object* v_fst_3901_; 
v_fst_3901_ = lean_ctor_get(v_____s_3900_, 0);
if (lean_obj_tag(v_fst_3901_) == 0)
{
lean_object* v_snd_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v_toPure_3899_);
v_snd_3902_ = lean_ctor_get(v_____s_3900_, 1);
lean_inc(v_snd_3902_);
lean_dec_ref(v_____s_3900_);
v___x_3903_ = l_Lean_NameSet_empty;
v___x_3904_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3896_, v_inst_3897_, v_fieldVal_x3f_3898_, v___x_3903_, v_snd_3902_);
return v___x_3904_;
}
else
{
lean_object* v_val_3905_; lean_object* v___x_3906_; 
lean_inc_ref(v_fst_3901_);
lean_dec_ref(v_____s_3900_);
lean_dec(v_fieldVal_x3f_3898_);
lean_dec(v_inst_3897_);
lean_dec_ref(v_inst_3896_);
v_val_3905_ = lean_ctor_get(v_fst_3901_, 0);
lean_inc(v_val_3905_);
lean_dec_ref_known(v_fst_3901_, 1);
v___x_3906_ = lean_apply_2(v_toPure_3899_, lean_box(0), v_val_3905_);
return v___x_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3907_, lean_object* v_a_3908_, lean_object* v___x_3909_, lean_object* v_toPure_3910_, lean_object* v_____r_3911_){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3912_ = lean_expr_instantiate1(v_body_3907_, v_a_3908_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3909_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = lean_apply_2(v_toPure_3910_, lean_box(0), v___x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3916_, lean_object* v_a_3917_, lean_object* v___x_3918_, lean_object* v_toPure_3919_, lean_object* v_____r_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3916_, v_a_3917_, v___x_3918_, v_toPure_3919_, v_____r_3920_);
lean_dec_ref(v_a_3917_);
lean_dec_ref(v_body_3916_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3924_, lean_object* v_toPure_3925_, lean_object* v___f_3926_, uint8_t v_____do__lift_3927_){
_start:
{
if (v_____do__lift_3927_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_dec(v___f_3926_);
v___x_3928_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v_snd_3924_);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
v___x_3931_ = lean_apply_2(v_toPure_3925_, lean_box(0), v___x_3930_);
return v___x_3931_;
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v_toPure_3925_);
lean_dec(v_snd_3924_);
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_apply_1(v___f_3926_, v___x_3932_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3934_, lean_object* v_toPure_3935_, lean_object* v___f_3936_, lean_object* v_____do__lift_3937_){
_start:
{
uint8_t v_____do__lift_852__boxed_3938_; lean_object* v_res_3939_; 
v_____do__lift_852__boxed_3938_ = lean_unbox(v_____do__lift_3937_);
v_res_3939_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3934_, v_toPure_3935_, v___f_3936_, v_____do__lift_852__boxed_3938_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3940_, lean_object* v_inst_3941_, lean_object* v_toBind_3942_, lean_object* v___f_3943_, lean_object* v_____do__lift_3944_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3945_, 0, v_____do__lift_3944_);
lean_closure_set(v___x_3945_, 1, v_binderType_3940_);
v___x_3946_ = lean_apply_2(v_inst_3941_, lean_box(0), v___x_3945_);
v___x_3947_ = lean_apply_4(v_toBind_3942_, lean_box(0), lean_box(0), v___x_3946_, v___f_3943_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3948_, lean_object* v_toPure_3949_, lean_object* v_levels_x3f_3950_, uint8_t v___x_3951_, lean_object* v_inst_3952_, lean_object* v_toBind_3953_, lean_object* v_a_3954_, lean_object* v_x_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_snd_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3978_; 
v_snd_3957_ = lean_ctor_get(v___y_3956_, 1);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___y_3956_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; 
v_unused_3979_ = lean_ctor_get(v___y_3956_, 0);
lean_dec(v_unused_3979_);
v___x_3959_ = v___y_3956_;
v_isShared_3960_ = v_isSharedCheck_3978_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_snd_3957_);
lean_dec(v___y_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3978_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
if (lean_obj_tag(v_snd_3957_) == 6)
{
lean_object* v_binderType_3961_; lean_object* v_body_3962_; lean_object* v___f_3963_; 
lean_del_object(v___x_3959_);
v_binderType_3961_ = lean_ctor_get(v_snd_3957_, 1);
lean_inc_ref(v_binderType_3961_);
v_body_3962_ = lean_ctor_get(v_snd_3957_, 2);
lean_inc(v_toPure_3949_);
lean_inc(v___x_3948_);
lean_inc_ref(v_a_3954_);
lean_inc_ref(v_body_3962_);
v___f_3963_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3963_, 0, v_body_3962_);
lean_closure_set(v___f_3963_, 1, v_a_3954_);
lean_closure_set(v___f_3963_, 2, v___x_3948_);
lean_closure_set(v___f_3963_, 3, v_toPure_3949_);
if (lean_obj_tag(v_levels_x3f_3950_) == 0)
{
if (v___x_3951_ == 0)
{
lean_inc_ref(v_body_3962_);
lean_dec_ref(v___f_3963_);
lean_dec_ref(v_binderType_3961_);
lean_dec_ref_known(v_snd_3957_, 3);
lean_dec(v_toBind_3953_);
lean_dec(v_inst_3952_);
goto v___jp_3964_;
}
else
{
lean_object* v___f_3967_; lean_object* v___f_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec(v___x_3948_);
v___f_3967_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3967_, 0, v_snd_3957_);
lean_closure_set(v___f_3967_, 1, v_toPure_3949_);
lean_closure_set(v___f_3967_, 2, v___f_3963_);
lean_inc(v_toBind_3953_);
lean_inc(v_inst_3952_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3968_, 0, v_binderType_3961_);
lean_closure_set(v___f_3968_, 1, v_inst_3952_);
lean_closure_set(v___f_3968_, 2, v_toBind_3953_);
lean_closure_set(v___f_3968_, 3, v___f_3967_);
v___x_3969_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3969_, 0, v_a_3954_);
v___x_3970_ = lean_apply_2(v_inst_3952_, lean_box(0), v___x_3969_);
v___x_3971_ = lean_apply_4(v_toBind_3953_, lean_box(0), lean_box(0), v___x_3970_, v___f_3968_);
return v___x_3971_;
}
}
else
{
lean_inc_ref(v_body_3962_);
lean_dec_ref(v___f_3963_);
lean_dec_ref(v_binderType_3961_);
lean_dec_ref_known(v_snd_3957_, 3);
lean_dec(v_toBind_3953_);
lean_dec(v_inst_3952_);
goto v___jp_3964_;
}
v___jp_3964_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_box(0);
v___x_3966_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3962_, v_a_3954_, v___x_3948_, v_toPure_3949_, v___x_3965_);
lean_dec_ref(v_a_3954_);
lean_dec_ref(v_body_3962_);
return v___x_3966_;
}
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
lean_dec_ref(v_a_3954_);
lean_dec(v_toBind_3953_);
lean_dec(v_inst_3952_);
lean_dec(v___x_3948_);
v___x_3972_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3972_);
v___x_3974_ = v___x_3959_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_snd_3957_);
v___x_3974_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
v___x_3976_ = lean_apply_2(v_toPure_3949_, lean_box(0), v___x_3975_);
return v___x_3976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3980_, lean_object* v_toPure_3981_, lean_object* v_levels_x3f_3982_, lean_object* v___x_3983_, lean_object* v_inst_3984_, lean_object* v_toBind_3985_, lean_object* v_a_3986_, lean_object* v_x_3987_, lean_object* v___y_3988_){
_start:
{
uint8_t v___x_888__boxed_3989_; lean_object* v_res_3990_; 
v___x_888__boxed_3989_ = lean_unbox(v___x_3983_);
v_res_3990_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3980_, v_toPure_3981_, v_levels_x3f_3982_, v___x_888__boxed_3989_, v_inst_3984_, v_toBind_3985_, v_a_3986_, v_x_3987_, v___y_3988_);
lean_dec(v_levels_x3f_3982_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3991_, lean_object* v_levels_x3f_3992_, uint8_t v___x_3993_, lean_object* v_inst_3994_, lean_object* v_toBind_3995_, lean_object* v_params_3996_, lean_object* v_inst_3997_, lean_object* v___f_3998_, lean_object* v_val_3999_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v___x_4003_; size_t v_sz_4004_; size_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_box(v___x_3993_);
lean_inc(v_toBind_3995_);
v___f_4002_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_4002_, 0, v___x_4000_);
lean_closure_set(v___f_4002_, 1, v_toPure_3991_);
lean_closure_set(v___f_4002_, 2, v_levels_x3f_3992_);
lean_closure_set(v___f_4002_, 3, v___x_4001_);
lean_closure_set(v___f_4002_, 4, v_inst_3994_);
lean_closure_set(v___f_4002_, 5, v_toBind_3995_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4000_);
lean_ctor_set(v___x_4003_, 1, v_val_3999_);
v_sz_4004_ = lean_array_size(v_params_3996_);
v___x_4005_ = ((size_t)0ULL);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3997_, v_params_3996_, v___f_4002_, v_sz_4004_, v___x_4005_, v___x_4003_);
v___x_4007_ = lean_apply_4(v_toBind_3995_, lean_box(0), lean_box(0), v___x_4006_, v___f_3998_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v_toPure_4008_, lean_object* v_levels_x3f_4009_, lean_object* v___x_4010_, lean_object* v_inst_4011_, lean_object* v_toBind_4012_, lean_object* v_params_4013_, lean_object* v_inst_4014_, lean_object* v___f_4015_, lean_object* v_val_4016_){
_start:
{
uint8_t v___x_950__boxed_4017_; lean_object* v_res_4018_; 
v___x_950__boxed_4017_ = lean_unbox(v___x_4010_);
v_res_4018_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v_toPure_4008_, v_levels_x3f_4009_, v___x_950__boxed_4017_, v_inst_4011_, v_toBind_4012_, v_params_4013_, v_inst_4014_, v___f_4015_, v_val_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4019_, lean_object* v_us_4020_, uint8_t v___x_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4019_, v_us_4020_, v___x_4021_, v___y_4024_, v___y_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4028_, lean_object* v_us_4029_, lean_object* v___x_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
uint8_t v___x_976__boxed_4036_; lean_object* v_res_4037_; 
v___x_976__boxed_4036_ = lean_unbox(v___x_4030_);
v_res_4037_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4028_, v_us_4029_, v___x_976__boxed_4036_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec_ref(v_cinfo_4028_);
return v_res_4037_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4041_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4042_ = lean_unsigned_to_nat(2u);
v___x_4043_ = lean_unsigned_to_nat(202u);
v___x_4044_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4045_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4046_ = l_mkPanicMessageWithDecl(v___x_4045_, v___x_4044_, v___x_4043_, v___x_4042_, v___x_4041_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4047_, lean_object* v_inst_4048_, lean_object* v_toPure_4049_, lean_object* v_levels_x3f_4050_, lean_object* v_inst_4051_, lean_object* v_toBind_4052_, lean_object* v_params_4053_, lean_object* v___f_4054_, lean_object* v_us_4055_){
_start:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v___x_4056_ = l_List_lengthTR___redArg(v_us_4055_);
v___x_4057_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4047_);
v___x_4058_ = l_List_lengthTR___redArg(v___x_4057_);
lean_dec(v___x_4057_);
v___x_4059_ = lean_nat_dec_eq(v___x_4056_, v___x_4058_);
lean_dec(v___x_4058_);
lean_dec(v___x_4056_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_dec(v_us_4055_);
lean_dec(v___f_4054_);
lean_dec_ref(v_params_4053_);
lean_dec(v_toBind_4052_);
lean_dec(v_inst_4051_);
lean_dec(v_levels_x3f_4050_);
lean_dec(v_toPure_4049_);
lean_dec_ref(v_cinfo_4047_);
v___x_4060_ = lean_box(0);
v___x_4061_ = l_instInhabitedOfMonad___redArg(v_inst_4048_, v___x_4060_);
v___x_4062_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4063_ = l_panic___redArg(v___x_4061_, v___x_4062_);
lean_dec(v___x_4061_);
return v___x_4063_;
}
else
{
lean_object* v___x_4064_; lean_object* v___f_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4064_ = lean_box(v___x_4059_);
lean_inc(v_toBind_4052_);
lean_inc(v_inst_4051_);
v___f_4065_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_4065_, 0, v_toPure_4049_);
lean_closure_set(v___f_4065_, 1, v_levels_x3f_4050_);
lean_closure_set(v___f_4065_, 2, v___x_4064_);
lean_closure_set(v___f_4065_, 3, v_inst_4051_);
lean_closure_set(v___f_4065_, 4, v_toBind_4052_);
lean_closure_set(v___f_4065_, 5, v_params_4053_);
lean_closure_set(v___f_4065_, 6, v_inst_4048_);
lean_closure_set(v___f_4065_, 7, v___f_4054_);
v___x_4066_ = 0;
v___x_4067_ = lean_box(v___x_4066_);
v___f_4068_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4068_, 0, v_cinfo_4047_);
lean_closure_set(v___f_4068_, 1, v_us_4055_);
lean_closure_set(v___f_4068_, 2, v___x_4067_);
v___x_4069_ = lean_apply_2(v_inst_4051_, lean_box(0), v___f_4068_);
v___x_4070_ = lean_apply_4(v_toBind_4052_, lean_box(0), lean_box(0), v___x_4069_, v___f_4065_);
return v___x_4070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4071_, lean_object* v_toPure_4072_, lean_object* v_levels_x3f_4073_, lean_object* v_inst_4074_, lean_object* v_toBind_4075_, lean_object* v_params_4076_, lean_object* v___f_4077_, lean_object* v_cinfo_4078_){
_start:
{
lean_object* v___f_4079_; 
lean_inc(v_toBind_4075_);
lean_inc(v_inst_4074_);
lean_inc(v_levels_x3f_4073_);
lean_inc(v_toPure_4072_);
lean_inc_ref(v_cinfo_4078_);
v___f_4079_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4079_, 0, v_cinfo_4078_);
lean_closure_set(v___f_4079_, 1, v_inst_4071_);
lean_closure_set(v___f_4079_, 2, v_toPure_4072_);
lean_closure_set(v___f_4079_, 3, v_levels_x3f_4073_);
lean_closure_set(v___f_4079_, 4, v_inst_4074_);
lean_closure_set(v___f_4079_, 5, v_toBind_4075_);
lean_closure_set(v___f_4079_, 6, v_params_4076_);
lean_closure_set(v___f_4079_, 7, v___f_4077_);
if (lean_obj_tag(v_levels_x3f_4073_) == 0)
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec(v_toPure_4072_);
v___x_4080_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4080_, 0, v_cinfo_4078_);
v___x_4081_ = lean_apply_2(v_inst_4074_, lean_box(0), v___x_4080_);
v___x_4082_ = lean_apply_4(v_toBind_4075_, lean_box(0), lean_box(0), v___x_4081_, v___f_4079_);
return v___x_4082_;
}
else
{
lean_object* v_val_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec_ref(v_cinfo_4078_);
lean_dec(v_inst_4074_);
v_val_4083_ = lean_ctor_get(v_levels_x3f_4073_, 0);
lean_inc(v_val_4083_);
lean_dec_ref_known(v_levels_x3f_4073_, 1);
v___x_4084_ = lean_apply_2(v_toPure_4072_, lean_box(0), v_val_4083_);
v___x_4085_ = lean_apply_4(v_toBind_4075_, lean_box(0), lean_box(0), v___x_4084_, v___f_4079_);
return v___x_4085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4086_, lean_object* v_inst_4087_, lean_object* v_inst_4088_, lean_object* v_inst_4089_, lean_object* v_defaultFn_4090_, lean_object* v_levels_x3f_4091_, lean_object* v_params_4092_, lean_object* v_fieldVal_x3f_4093_){
_start:
{
lean_object* v_toApplicative_4094_; lean_object* v_toBind_4095_; lean_object* v_toPure_4096_; lean_object* v___x_4097_; lean_object* v___f_4098_; lean_object* v___f_4099_; lean_object* v___x_4100_; 
v_toApplicative_4094_ = lean_ctor_get(v_inst_4086_, 0);
v_toBind_4095_ = lean_ctor_get(v_inst_4086_, 1);
lean_inc_n(v_toBind_4095_, 2);
v_toPure_4096_ = lean_ctor_get(v_toApplicative_4094_, 1);
lean_inc_n(v_toPure_4096_, 2);
lean_inc_ref_n(v_inst_4086_, 2);
v___x_4097_ = l_Lean_getConstInfo___redArg(v_inst_4086_, v_inst_4087_, v_inst_4088_, v_defaultFn_4090_);
lean_inc(v_inst_4089_);
v___f_4098_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4098_, 0, v_inst_4086_);
lean_closure_set(v___f_4098_, 1, v_inst_4089_);
lean_closure_set(v___f_4098_, 2, v_fieldVal_x3f_4093_);
lean_closure_set(v___f_4098_, 3, v_toPure_4096_);
v___f_4099_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4099_, 0, v_inst_4086_);
lean_closure_set(v___f_4099_, 1, v_toPure_4096_);
lean_closure_set(v___f_4099_, 2, v_levels_x3f_4091_);
lean_closure_set(v___f_4099_, 3, v_inst_4089_);
lean_closure_set(v___f_4099_, 4, v_toBind_4095_);
lean_closure_set(v___f_4099_, 5, v_params_4092_);
lean_closure_set(v___f_4099_, 6, v___f_4098_);
v___x_4100_ = lean_apply_4(v_toBind_4095_, lean_box(0), lean_box(0), v___x_4097_, v___f_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4101_, lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_inst_4104_, lean_object* v_inst_4105_, lean_object* v_inst_4106_, lean_object* v_defaultFn_4107_, lean_object* v_levels_x3f_4108_, lean_object* v_params_4109_, lean_object* v_fieldVal_x3f_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4102_, v_inst_4103_, v_inst_4104_, v_inst_4105_, v_defaultFn_4107_, v_levels_x3f_4108_, v_params_4109_, v_fieldVal_x3f_4110_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4112_, lean_object* v_inst_4113_, lean_object* v_inst_4114_, lean_object* v_inst_4115_, lean_object* v_inst_4116_, lean_object* v_inst_4117_, lean_object* v_defaultFn_4118_, lean_object* v_levels_x3f_4119_, lean_object* v_params_4120_, lean_object* v_fieldVal_x3f_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4112_, v_inst_4113_, v_inst_4114_, v_inst_4115_, v_inst_4116_, v_inst_4117_, v_defaultFn_4118_, v_levels_x3f_4119_, v_params_4120_, v_fieldVal_x3f_4121_);
lean_dec_ref(v_inst_4117_);
return v_res_4122_;
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
