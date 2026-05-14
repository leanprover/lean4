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
uint8_t lean_is_out_param(lean_object*);
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
lean_dec_ref(v___x_62_);
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
lean_dec_ref(v___x_405_);
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
lean_dec_ref(v___x_443_);
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
uint8_t v___x_18745__boxed_466_; lean_object* v_res_467_; 
v___x_18745__boxed_466_ = lean_unbox(v___x_456_);
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_18745__boxed_466_, v_projName_457_, v_n_458_, v_ref_459_, v___f_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
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
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_traceState_485_; lean_object* v_messages_486_; lean_object* v_infoState_487_; lean_object* v_snapshotTasks_488_; lean_object* v_newDecls_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_518_; 
v___x_480_ = lean_st_ref_take(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_480_, 1);
v_ngen_483_ = lean_ctor_get(v___x_480_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_480_, 3);
v_traceState_485_ = lean_ctor_get(v___x_480_, 4);
v_messages_486_ = lean_ctor_get(v___x_480_, 6);
v_infoState_487_ = lean_ctor_get(v___x_480_, 7);
v_snapshotTasks_488_ = lean_ctor_get(v___x_480_, 8);
v_newDecls_489_ = lean_ctor_get(v___x_480_, 9);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v___x_480_, 5);
lean_dec(v_unused_519_);
v___x_491_ = v___x_480_;
v_isShared_492_ = v_isSharedCheck_518_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_newDecls_489_);
lean_inc(v_snapshotTasks_488_);
lean_inc(v_infoState_487_);
lean_inc(v_messages_486_);
lean_inc(v_traceState_485_);
lean_inc(v_auxDeclNGen_484_);
lean_inc(v_ngen_483_);
lean_inc(v_nextMacroScope_482_);
lean_inc(v_env_481_);
lean_dec(v___x_480_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_518_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_493_ = 0;
v___x_494_ = lean_box(0);
v___x_495_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_481_, v_declName_475_, v_s_476_, v___x_493_, v___x_494_);
v___x_496_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 5, v___x_496_);
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_traceState_485_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_messages_486_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v_infoState_487_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_snapshotTasks_488_);
lean_ctor_set(v_reuseFailAlloc_517_, 9, v_newDecls_489_);
v___x_498_ = v_reuseFailAlloc_517_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_mctx_501_; lean_object* v_zetaDeltaFVarIds_502_; lean_object* v_postponed_503_; lean_object* v_diag_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v___x_499_ = lean_st_ref_set(v___y_478_, v___x_498_);
v___x_500_ = lean_st_ref_take(v___y_477_);
v_mctx_501_ = lean_ctor_get(v___x_500_, 0);
v_zetaDeltaFVarIds_502_ = lean_ctor_get(v___x_500_, 2);
v_postponed_503_ = lean_ctor_get(v___x_500_, 3);
v_diag_504_ = lean_ctor_get(v___x_500_, 4);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_500_, 1);
lean_dec(v_unused_516_);
v___x_506_ = v___x_500_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_diag_504_);
lean_inc(v_postponed_503_);
lean_inc(v_zetaDeltaFVarIds_502_);
lean_inc(v_mctx_501_);
lean_dec(v___x_500_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_mctx_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_zetaDeltaFVarIds_502_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_postponed_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_diag_504_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_st_ref_set(v___y_477_, v___x_510_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_520_, lean_object* v_s_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_s_boxed_525_; lean_object* v_res_526_; 
v_s_boxed_525_ = lean_unbox(v_s_521_);
v_res_526_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_520_, v_s_boxed_525_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec(v___y_522_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = 0;
v___x_534_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_527_, v___x_533_, v___y_529_, v___y_531_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_551_, lean_object* v_projName_552_, lean_object* v___x_553_, lean_object* v_a_554_, uint8_t v_instImplicit_555_, lean_object* v___x_556_, lean_object* v_params_557_, lean_object* v_self_558_, lean_object* v_b_559_, uint8_t v___x_560_, lean_object* v_a_561_, lean_object* v___x_562_, lean_object* v_paramInfoOverrides_563_, lean_object* v_n_564_, lean_object* v_ref_565_, lean_object* v___x_566_, uint8_t v_a_567_, lean_object* v_____r_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_633_; lean_object* v___y_634_; uint8_t v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_List_lengthTR___redArg(v_paramInfoOverrides_563_);
v___x_739_ = lean_array_get_size(v_params_557_);
v___x_740_ = lean_nat_dec_le(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_552_);
v___x_742_ = l_Lean_MessageData_ofName(v_projName_552_);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_inc(v_n_564_);
v___x_746_ = l_Lean_MessageData_ofConstName(v_n_564_, v___x_740_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_565_, v___x_749_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_dec_ref(v___x_750_);
goto v___jp_699_;
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_566_);
lean_dec(v_n_564_);
lean_dec_ref(v_a_561_);
lean_dec_ref(v_self_558_);
lean_dec(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v___x_553_);
lean_dec(v_projName_552_);
lean_dec_ref(v___x_551_);
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
goto v___jp_699_;
}
v___jp_574_:
{
lean_object* v___x_577_; lean_object* v_env_578_; lean_object* v_nextMacroScope_579_; lean_object* v_ngen_580_; lean_object* v_auxDeclNGen_581_; lean_object* v_traceState_582_; lean_object* v_messages_583_; lean_object* v_infoState_584_; lean_object* v_snapshotTasks_585_; lean_object* v_newDecls_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_618_; 
v___x_577_ = lean_st_ref_take(v___y_576_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
v_nextMacroScope_579_ = lean_ctor_get(v___x_577_, 1);
v_ngen_580_ = lean_ctor_get(v___x_577_, 2);
v_auxDeclNGen_581_ = lean_ctor_get(v___x_577_, 3);
v_traceState_582_ = lean_ctor_get(v___x_577_, 4);
v_messages_583_ = lean_ctor_get(v___x_577_, 6);
v_infoState_584_ = lean_ctor_get(v___x_577_, 7);
v_snapshotTasks_585_ = lean_ctor_get(v___x_577_, 8);
v_newDecls_586_ = lean_ctor_get(v___x_577_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v___x_577_, 5);
lean_dec(v_unused_619_);
v___x_588_ = v___x_577_;
v_isShared_589_ = v_isSharedCheck_618_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_newDecls_586_);
lean_inc(v_snapshotTasks_585_);
lean_inc(v_infoState_584_);
lean_inc(v_messages_583_);
lean_inc(v_traceState_582_);
lean_inc(v_auxDeclNGen_581_);
lean_inc(v_ngen_580_);
lean_inc(v_nextMacroScope_579_);
lean_inc(v_env_578_);
lean_dec(v___x_577_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_618_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_name_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_name_590_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_name_590_);
lean_dec_ref(v___x_551_);
lean_inc(v_projName_552_);
v___x_591_ = l_Lean_addProjectionFnInfo(v_env_578_, v_projName_552_, v_name_590_, v___x_553_, v_a_554_, v_instImplicit_555_);
v___x_592_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 5, v___x_592_);
lean_ctor_set(v___x_588_, 0, v___x_591_);
v___x_594_ = v___x_588_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_nextMacroScope_579_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_ngen_580_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_auxDeclNGen_581_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_traceState_582_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_messages_583_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_infoState_584_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_snapshotTasks_585_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_newDecls_586_);
v___x_594_ = v_reuseFailAlloc_617_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_mctx_597_; lean_object* v_zetaDeltaFVarIds_598_; lean_object* v_postponed_599_; lean_object* v_diag_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_615_; 
v___x_595_ = lean_st_ref_set(v___y_576_, v___x_594_);
v___x_596_ = lean_st_ref_take(v___y_575_);
v_mctx_597_ = lean_ctor_get(v___x_596_, 0);
v_zetaDeltaFVarIds_598_ = lean_ctor_get(v___x_596_, 2);
v_postponed_599_ = lean_ctor_get(v___x_596_, 3);
v_diag_600_ = lean_ctor_get(v___x_596_, 4);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v___x_596_, 1);
lean_dec(v_unused_616_);
v___x_602_ = v___x_596_;
v_isShared_603_ = v_isSharedCheck_615_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_diag_600_);
lean_inc(v_postponed_599_);
lean_inc(v_zetaDeltaFVarIds_598_);
lean_inc(v_mctx_597_);
lean_dec(v___x_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_615_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_mctx_597_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_zetaDeltaFVarIds_598_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_postponed_599_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_diag_600_);
v___x_606_ = v_reuseFailAlloc_614_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_607_ = lean_st_ref_set(v___y_575_, v___x_606_);
v___x_608_ = l_Lean_Expr_const___override(v_projName_552_, v___x_556_);
v___x_609_ = l_Lean_mkAppN(v___x_608_, v_params_557_);
v___x_610_ = l_Lean_Expr_app___override(v___x_609_, v_self_558_);
v___x_611_ = l_Lean_Expr_bindingBody_x21(v_b_559_);
v___x_612_ = lean_expr_instantiate1(v___x_611_, v___x_610_);
lean_dec_ref(v___x_610_);
lean_dec_ref(v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
}
}
v___jp_620_:
{
if (lean_obj_tag(v___y_623_) == 0)
{
lean_dec_ref(v___y_623_);
v___y_575_ = v___y_621_;
v___y_576_ = v___y_622_;
goto v___jp_574_;
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_self_558_);
lean_dec(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v___x_553_);
lean_dec(v_projName_552_);
lean_dec_ref(v___x_551_);
v_a_624_ = lean_ctor_get(v___y_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___y_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___y_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___y_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
v___jp_632_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_639_ = lean_box(0);
lean_inc(v_projName_552_);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v_projName_552_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_641_, 0, v___y_633_);
lean_ctor_set(v___x_641_, 1, v___y_637_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*3, v___x_560_);
v___x_642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
v___x_643_ = l_Lean_addDecl(v___x_642_, v___y_635_, v___y_638_, v___y_636_);
lean_dec_ref(v___y_638_);
v___y_621_ = v___y_634_;
v___y_622_ = v___y_636_;
v___y_623_ = v___x_643_;
goto v___jp_620_;
}
v___jp_644_:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v_fileName_653_; lean_object* v_fileMap_654_; lean_object* v_options_655_; lean_object* v_currRecDepth_656_; lean_object* v_maxRecDepth_657_; lean_object* v_ref_658_; lean_object* v_currNamespace_659_; lean_object* v_openDecls_660_; lean_object* v_initHeartbeats_661_; lean_object* v_maxHeartbeats_662_; lean_object* v_quotContext_663_; lean_object* v_currMacroScope_664_; uint8_t v_diag_665_; lean_object* v_cancelTk_x3f_666_; uint8_t v_suppressElabErrors_667_; lean_object* v_inheritedTraceOptions_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_ref_673_; lean_object* v___x_674_; 
v___x_651_ = 0;
lean_inc_ref(v_a_561_);
v___x_652_ = l_Lean_LocalContext_mkForall(v_a_561_, v___x_562_, v___y_646_, v___x_560_, v___x_651_);
lean_dec_ref(v___y_646_);
v_fileName_653_ = lean_ctor_get(v___y_649_, 0);
v_fileMap_654_ = lean_ctor_get(v___y_649_, 1);
v_options_655_ = lean_ctor_get(v___y_649_, 2);
v_currRecDepth_656_ = lean_ctor_get(v___y_649_, 3);
v_maxRecDepth_657_ = lean_ctor_get(v___y_649_, 4);
v_ref_658_ = lean_ctor_get(v___y_649_, 5);
v_currNamespace_659_ = lean_ctor_get(v___y_649_, 6);
v_openDecls_660_ = lean_ctor_get(v___y_649_, 7);
v_initHeartbeats_661_ = lean_ctor_get(v___y_649_, 8);
v_maxHeartbeats_662_ = lean_ctor_get(v___y_649_, 9);
v_quotContext_663_ = lean_ctor_get(v___y_649_, 10);
v_currMacroScope_664_ = lean_ctor_get(v___y_649_, 11);
v_diag_665_ = lean_ctor_get_uint8(v___y_649_, sizeof(void*)*14);
v_cancelTk_x3f_666_ = lean_ctor_get(v___y_649_, 12);
v_suppressElabErrors_667_ = lean_ctor_get_uint8(v___y_649_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_668_ = lean_ctor_get(v___y_649_, 13);
v___x_669_ = l_Lean_Expr_inferImplicit(v___x_652_, v___x_553_, v___x_560_);
v___x_670_ = l_Lean_Expr_updateForallBinderInfos(v___x_669_, v_paramInfoOverrides_563_);
lean_inc_ref(v_self_558_);
lean_inc(v_a_554_);
v___x_671_ = l_Lean_Expr_proj___override(v_n_564_, v_a_554_, v_self_558_);
v___x_672_ = l_Lean_LocalContext_mkLambda(v_a_561_, v___x_562_, v___x_671_, v___x_560_, v___x_651_);
lean_dec_ref(v___x_671_);
v_ref_673_ = l_Lean_replaceRef(v_ref_565_, v_ref_658_);
lean_inc_ref(v_inheritedTraceOptions_668_);
lean_inc(v_cancelTk_x3f_666_);
lean_inc(v_currMacroScope_664_);
lean_inc(v_quotContext_663_);
lean_inc(v_maxHeartbeats_662_);
lean_inc(v_initHeartbeats_661_);
lean_inc(v_openDecls_660_);
lean_inc(v_currNamespace_659_);
lean_inc(v_maxRecDepth_657_);
lean_inc(v_currRecDepth_656_);
lean_inc_ref(v_options_655_);
lean_inc_ref(v_fileMap_654_);
lean_inc_ref(v_fileName_653_);
v___x_674_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_674_, 0, v_fileName_653_);
lean_ctor_set(v___x_674_, 1, v_fileMap_654_);
lean_ctor_set(v___x_674_, 2, v_options_655_);
lean_ctor_set(v___x_674_, 3, v_currRecDepth_656_);
lean_ctor_set(v___x_674_, 4, v_maxRecDepth_657_);
lean_ctor_set(v___x_674_, 5, v_ref_673_);
lean_ctor_set(v___x_674_, 6, v_currNamespace_659_);
lean_ctor_set(v___x_674_, 7, v_openDecls_660_);
lean_ctor_set(v___x_674_, 8, v_initHeartbeats_661_);
lean_ctor_set(v___x_674_, 9, v_maxHeartbeats_662_);
lean_ctor_set(v___x_674_, 10, v_quotContext_663_);
lean_ctor_set(v___x_674_, 11, v_currMacroScope_664_);
lean_ctor_set(v___x_674_, 12, v_cancelTk_x3f_666_);
lean_ctor_set(v___x_674_, 13, v_inheritedTraceOptions_668_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*14, v_diag_665_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*14 + 1, v_suppressElabErrors_667_);
if (v___y_645_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_box(1);
lean_inc(v_projName_552_);
v___x_676_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_552_, v___x_566_, v___x_670_, v___x_672_, v___x_675_, v___y_650_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v_a_677_);
v___x_679_ = l_Lean_addDecl(v___x_678_, v___x_651_, v___x_674_, v___y_650_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec_ref(v___x_679_);
if (v_instImplicit_555_ == 0)
{
lean_object* v___x_680_; 
lean_inc(v_projName_552_);
v___x_680_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_552_, v___y_647_, v___y_648_, v___x_674_, v___y_650_);
lean_dec_ref(v___x_674_);
v___y_621_ = v___y_648_;
v___y_622_ = v___y_650_;
v___y_623_ = v___x_680_;
goto v___jp_620_;
}
else
{
lean_dec_ref(v___x_674_);
v___y_575_ = v___y_648_;
v___y_576_ = v___y_650_;
goto v___jp_574_;
}
}
else
{
lean_dec_ref(v___x_674_);
v___y_621_ = v___y_648_;
v___y_622_ = v___y_650_;
v___y_623_ = v___x_679_;
goto v___jp_620_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v___x_674_);
lean_dec_ref(v_self_558_);
lean_dec(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v___x_553_);
lean_dec(v_projName_552_);
lean_dec_ref(v___x_551_);
v_a_681_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_676_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_676_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v_env_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_689_ = lean_st_ref_get(v___y_650_);
v_env_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref_n(v_env_690_, 2);
lean_dec(v___x_689_);
lean_inc_ref(v___x_670_);
lean_inc(v_projName_552_);
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v_projName_552_);
lean_ctor_set(v___x_691_, 1, v___x_566_);
lean_ctor_set(v___x_691_, 2, v___x_670_);
v___x_692_ = l_Lean_Environment_hasUnsafe(v_env_690_, v___x_670_);
lean_dec_ref(v___x_670_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Environment_hasUnsafe(v_env_690_, v___x_672_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = lean_box(0);
lean_inc(v_projName_552_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v_projName_552_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
lean_ctor_set(v___x_696_, 1, v___x_672_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
v___x_697_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
v___x_698_ = l_Lean_addDecl(v___x_697_, v___x_651_, v___x_674_, v___y_650_);
lean_dec_ref(v___x_674_);
v___y_621_ = v___y_648_;
v___y_622_ = v___y_650_;
v___y_623_ = v___x_698_;
goto v___jp_620_;
}
else
{
v___y_633_ = v___x_691_;
v___y_634_ = v___y_648_;
v___y_635_ = v___x_651_;
v___y_636_ = v___y_650_;
v___y_637_ = v___x_672_;
v___y_638_ = v___x_674_;
goto v___jp_632_;
}
}
else
{
lean_dec_ref(v_env_690_);
v___y_633_ = v___x_691_;
v___y_634_ = v___y_648_;
v___y_635_ = v___x_651_;
v___y_636_ = v___y_650_;
v___y_637_ = v___x_672_;
v___y_638_ = v___x_674_;
goto v___jp_632_;
}
}
}
v___jp_699_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_Expr_bindingDomain_x21(v_b_559_);
v___x_701_ = lean_expr_consume_type_annotations(v___x_700_);
lean_inc_ref(v___x_701_);
v___x_702_ = l_Lean_Meta_isProp(v___x_701_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_702_) == 0)
{
if (v_a_567_ == 0)
{
lean_object* v_a_703_; uint8_t v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_704_ = lean_unbox(v_a_703_);
lean_dec(v_a_703_);
v___y_645_ = v___x_704_;
v___y_646_ = v___x_701_;
v___y_647_ = v___y_569_;
v___y_648_ = v___y_570_;
v___y_649_ = v___y_571_;
v___y_650_ = v___y_572_;
goto v___jp_644_;
}
else
{
lean_object* v_a_705_; uint8_t v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_702_);
v___x_706_ = lean_unbox(v_a_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_707_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_552_);
v___x_708_ = l_Lean_MessageData_ofName(v_projName_552_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_unbox(v_a_705_);
lean_inc(v_n_564_);
v___x_713_ = l_Lean_MessageData_ofConstName(v_n_564_, v___x_712_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_711_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
lean_inc_ref(v___x_701_);
v___x_717_ = l_Lean_indentExpr(v___x_701_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_565_, v___x_718_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_719_) == 0)
{
uint8_t v___x_720_; 
lean_dec_ref(v___x_719_);
v___x_720_ = lean_unbox(v_a_705_);
lean_dec(v_a_705_);
v___y_645_ = v___x_720_;
v___y_646_ = v___x_701_;
v___y_647_ = v___y_569_;
v___y_648_ = v___y_570_;
v___y_649_ = v___y_571_;
v___y_650_ = v___y_572_;
goto v___jp_644_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_705_);
lean_dec_ref(v___x_701_);
lean_dec(v___x_566_);
lean_dec(v_n_564_);
lean_dec_ref(v_a_561_);
lean_dec_ref(v_self_558_);
lean_dec(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v___x_553_);
lean_dec(v_projName_552_);
lean_dec_ref(v___x_551_);
v_a_721_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_719_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_719_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
uint8_t v___x_729_; 
v___x_729_ = lean_unbox(v_a_705_);
lean_dec(v_a_705_);
v___y_645_ = v___x_729_;
v___y_646_ = v___x_701_;
v___y_647_ = v___y_569_;
v___y_648_ = v___y_570_;
v___y_649_ = v___y_571_;
v___y_650_ = v___y_572_;
goto v___jp_644_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v___x_701_);
lean_dec(v___x_566_);
lean_dec(v_n_564_);
lean_dec_ref(v_a_561_);
lean_dec_ref(v_self_558_);
lean_dec(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v___x_553_);
lean_dec(v_projName_552_);
lean_dec_ref(v___x_551_);
v_a_730_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_702_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_702_);
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
uint8_t v_instImplicit_boxed_782_; uint8_t v___x_18984__boxed_783_; uint8_t v_a_18990__boxed_784_; lean_object* v_res_785_; 
v_instImplicit_boxed_782_ = lean_unbox(v_instImplicit_763_);
v___x_18984__boxed_783_ = lean_unbox(v___x_768_);
v_a_18990__boxed_784_ = lean_unbox(v_a_775_);
v_res_785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_759_, v_projName_760_, v___x_761_, v_a_762_, v_instImplicit_boxed_782_, v___x_764_, v_params_765_, v_self_766_, v_b_767_, v___x_18984__boxed_783_, v_a_769_, v___x_770_, v_paramInfoOverrides_771_, v_n_772_, v_ref_773_, v___x_774_, v_a_18990__boxed_784_, v_____r_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
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
lean_object* v___x_793_; lean_object* v_env_794_; lean_object* v_nextMacroScope_795_; lean_object* v_ngen_796_; lean_object* v_auxDeclNGen_797_; lean_object* v_traceState_798_; lean_object* v_messages_799_; lean_object* v_infoState_800_; lean_object* v_snapshotTasks_801_; lean_object* v_newDecls_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_827_; 
v___x_793_ = lean_st_ref_take(v___y_786_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
v_nextMacroScope_795_ = lean_ctor_get(v___x_793_, 1);
v_ngen_796_ = lean_ctor_get(v___x_793_, 2);
v_auxDeclNGen_797_ = lean_ctor_get(v___x_793_, 3);
v_traceState_798_ = lean_ctor_get(v___x_793_, 4);
v_messages_799_ = lean_ctor_get(v___x_793_, 6);
v_infoState_800_ = lean_ctor_get(v___x_793_, 7);
v_snapshotTasks_801_ = lean_ctor_get(v___x_793_, 8);
v_newDecls_802_ = lean_ctor_get(v___x_793_, 9);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_793_, 5);
lean_dec(v_unused_828_);
v___x_804_ = v___x_793_;
v_isShared_805_ = v_isSharedCheck_827_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_newDecls_802_);
lean_inc(v_snapshotTasks_801_);
lean_inc(v_infoState_800_);
lean_inc(v_messages_799_);
lean_inc(v_traceState_798_);
lean_inc(v_auxDeclNGen_797_);
lean_inc(v_ngen_796_);
lean_inc(v_nextMacroScope_795_);
lean_inc(v_env_794_);
lean_dec(v___x_793_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_827_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = l_Lean_Environment_setExporting(v_env_794_, v_isExporting_787_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 5, v___x_788_);
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_nextMacroScope_795_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_ngen_796_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v_auxDeclNGen_797_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_traceState_798_);
lean_ctor_set(v_reuseFailAlloc_826_, 5, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_826_, 6, v_messages_799_);
lean_ctor_set(v_reuseFailAlloc_826_, 7, v_infoState_800_);
lean_ctor_set(v_reuseFailAlloc_826_, 8, v_snapshotTasks_801_);
lean_ctor_set(v_reuseFailAlloc_826_, 9, v_newDecls_802_);
v___x_808_ = v_reuseFailAlloc_826_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_mctx_811_; lean_object* v_zetaDeltaFVarIds_812_; lean_object* v_postponed_813_; lean_object* v_diag_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_824_; 
v___x_809_ = lean_st_ref_set(v___y_786_, v___x_808_);
v___x_810_ = lean_st_ref_take(v___y_789_);
v_mctx_811_ = lean_ctor_get(v___x_810_, 0);
v_zetaDeltaFVarIds_812_ = lean_ctor_get(v___x_810_, 2);
v_postponed_813_ = lean_ctor_get(v___x_810_, 3);
v_diag_814_ = lean_ctor_get(v___x_810_, 4);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_810_, 1);
lean_dec(v_unused_825_);
v___x_816_ = v___x_810_;
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_diag_814_);
lean_inc(v_postponed_813_);
lean_inc(v_zetaDeltaFVarIds_812_);
lean_inc(v_mctx_811_);
lean_dec(v___x_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_824_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_790_);
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_mctx_811_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_zetaDeltaFVarIds_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_postponed_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_diag_814_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_st_ref_set(v___y_789_, v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_829_, lean_object* v_isExporting_830_, lean_object* v___x_831_, lean_object* v___y_832_, lean_object* v___x_833_, lean_object* v_a_x3f_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_isExporting_boxed_836_; lean_object* v_res_837_; 
v_isExporting_boxed_836_ = lean_unbox(v_isExporting_830_);
v_res_837_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_829_, v_isExporting_boxed_836_, v___x_831_, v___y_832_, v___x_833_, v_a_x3f_834_);
lean_dec(v_a_x3f_834_);
lean_dec(v___y_832_);
lean_dec(v___y_829_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_838_, uint8_t v_isExporting_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_env_846_; uint8_t v_isExporting_847_; lean_object* v___x_848_; lean_object* v_env_849_; lean_object* v_nextMacroScope_850_; lean_object* v_ngen_851_; lean_object* v_auxDeclNGen_852_; lean_object* v_traceState_853_; lean_object* v_messages_854_; lean_object* v_infoState_855_; lean_object* v_snapshotTasks_856_; lean_object* v_newDecls_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_911_; 
v___x_845_ = lean_st_ref_get(v___y_843_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc_ref(v_env_846_);
lean_dec(v___x_845_);
v_isExporting_847_ = lean_ctor_get_uint8(v_env_846_, sizeof(void*)*8);
lean_dec_ref(v_env_846_);
v___x_848_ = lean_st_ref_take(v___y_843_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
v_nextMacroScope_850_ = lean_ctor_get(v___x_848_, 1);
v_ngen_851_ = lean_ctor_get(v___x_848_, 2);
v_auxDeclNGen_852_ = lean_ctor_get(v___x_848_, 3);
v_traceState_853_ = lean_ctor_get(v___x_848_, 4);
v_messages_854_ = lean_ctor_get(v___x_848_, 6);
v_infoState_855_ = lean_ctor_get(v___x_848_, 7);
v_snapshotTasks_856_ = lean_ctor_get(v___x_848_, 8);
v_newDecls_857_ = lean_ctor_get(v___x_848_, 9);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_848_, 5);
lean_dec(v_unused_912_);
v___x_859_ = v___x_848_;
v_isShared_860_ = v_isSharedCheck_911_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_newDecls_857_);
lean_inc(v_snapshotTasks_856_);
lean_inc(v_infoState_855_);
lean_inc(v_messages_854_);
lean_inc(v_traceState_853_);
lean_inc(v_auxDeclNGen_852_);
lean_inc(v_ngen_851_);
lean_inc(v_nextMacroScope_850_);
lean_inc(v_env_849_);
lean_dec(v___x_848_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_911_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = l_Lean_Environment_setExporting(v_env_849_, v_isExporting_839_);
v___x_862_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 5, v___x_862_);
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_nextMacroScope_850_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_ngen_851_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_auxDeclNGen_852_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_traceState_853_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_910_, 6, v_messages_854_);
lean_ctor_set(v_reuseFailAlloc_910_, 7, v_infoState_855_);
lean_ctor_set(v_reuseFailAlloc_910_, 8, v_snapshotTasks_856_);
lean_ctor_set(v_reuseFailAlloc_910_, 9, v_newDecls_857_);
v___x_864_ = v_reuseFailAlloc_910_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_mctx_867_; lean_object* v_zetaDeltaFVarIds_868_; lean_object* v_postponed_869_; lean_object* v_diag_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_908_; 
v___x_865_ = lean_st_ref_set(v___y_843_, v___x_864_);
v___x_866_ = lean_st_ref_take(v___y_841_);
v_mctx_867_ = lean_ctor_get(v___x_866_, 0);
v_zetaDeltaFVarIds_868_ = lean_ctor_get(v___x_866_, 2);
v_postponed_869_ = lean_ctor_get(v___x_866_, 3);
v_diag_870_ = lean_ctor_get(v___x_866_, 4);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v___x_866_, 1);
lean_dec(v_unused_909_);
v___x_872_ = v___x_866_;
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_diag_870_);
lean_inc(v_postponed_869_);
lean_inc(v_zetaDeltaFVarIds_868_);
lean_inc(v_mctx_867_);
lean_dec(v___x_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_mctx_867_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_zetaDeltaFVarIds_868_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_postponed_869_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_diag_870_);
v___x_876_ = v_reuseFailAlloc_907_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v_r_878_; 
v___x_877_ = lean_st_ref_set(v___y_841_, v___x_876_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
v_r_878_ = lean_apply_5(v_x_838_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, lean_box(0));
if (lean_obj_tag(v_r_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_895_; 
v_a_879_ = lean_ctor_get(v_r_878_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_r_878_);
if (v_isSharedCheck_895_ == 0)
{
v___x_881_ = v_r_878_;
v_isShared_882_ = v_isSharedCheck_895_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v_r_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_895_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
lean_inc(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 1);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_894_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v___x_885_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_843_, v_isExporting_847_, v___x_862_, v___y_841_, v___x_874_, v___x_884_);
lean_dec_ref(v___x_884_);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_885_, 0);
lean_dec(v_unused_893_);
v___x_887_ = v___x_885_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_dec(v___x_885_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_a_879_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_879_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
v_a_896_ = lean_ctor_get(v_r_878_, 0);
lean_inc(v_a_896_);
lean_dec_ref(v_r_878_);
v___x_897_ = lean_box(0);
v___x_898_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_843_, v_isExporting_847_, v___x_862_, v___y_841_, v___x_874_, v___x_897_);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_898_, 0);
lean_dec(v_unused_906_);
v___x_900_ = v___x_898_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_898_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 0, v_a_896_);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_896_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_913_, lean_object* v_isExporting_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v_isExporting_boxed_920_; lean_object* v_res_921_; 
v_isExporting_boxed_920_ = lean_unbox(v_isExporting_914_);
v_res_921_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_913_, v_isExporting_boxed_920_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_922_, uint8_t v_when_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
if (v_when_923_ == 0)
{
lean_object* v___x_929_; 
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_929_ = lean_apply_5(v_x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_929_;
}
else
{
uint8_t v___x_930_; lean_object* v___x_931_; 
v___x_930_ = 0;
v___x_931_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_922_, v___x_930_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_932_, lean_object* v_when_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v_when_boxed_939_; lean_object* v_res_940_; 
v_when_boxed_939_ = lean_unbox(v_when_933_);
v_res_940_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_932_, v_when_boxed_939_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_941_, lean_object* v_projDecls_942_, lean_object* v___x_943_, lean_object* v___x_944_, uint8_t v_instImplicit_945_, lean_object* v___x_946_, lean_object* v_params_947_, lean_object* v_self_948_, lean_object* v_a_949_, lean_object* v___x_950_, lean_object* v_n_951_, lean_object* v___x_952_, uint8_t v_a_953_, lean_object* v_a_954_, lean_object* v_b_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_lt(v_a_954_, v_upperBound_941_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec(v_a_954_);
lean_dec(v___x_952_);
lean_dec(v_n_951_);
lean_dec_ref(v___x_950_);
lean_dec_ref(v_a_949_);
lean_dec_ref(v_self_948_);
lean_dec_ref(v_params_947_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec_ref(v___x_943_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_b_955_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v_ref_964_; lean_object* v_projName_965_; lean_object* v_paramInfoOverrides_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___f_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___y_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_963_ = lean_array_fget_borrowed(v_projDecls_942_, v_a_954_);
v_ref_964_ = lean_ctor_get(v___x_963_, 0);
v_projName_965_ = lean_ctor_get(v___x_963_, 1);
v_paramInfoOverrides_966_ = lean_ctor_get(v___x_963_, 2);
v___x_967_ = lean_box(v_instImplicit_945_);
v___x_968_ = lean_box(v___x_961_);
v___x_969_ = lean_box(v_a_953_);
lean_inc(v___x_952_);
lean_inc_n(v_ref_964_, 2);
lean_inc_n(v_n_951_, 2);
lean_inc(v_paramInfoOverrides_966_);
lean_inc_ref(v___x_950_);
lean_inc_ref(v_a_949_);
lean_inc_ref(v_b_955_);
lean_inc_ref(v_self_948_);
lean_inc_ref(v_params_947_);
lean_inc(v___x_946_);
lean_inc(v_a_954_);
lean_inc(v___x_944_);
lean_inc_n(v_projName_965_, 2);
lean_inc_ref(v___x_943_);
v___f_970_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_970_, 0, v___x_943_);
lean_closure_set(v___f_970_, 1, v_projName_965_);
lean_closure_set(v___f_970_, 2, v___x_944_);
lean_closure_set(v___f_970_, 3, v_a_954_);
lean_closure_set(v___f_970_, 4, v___x_967_);
lean_closure_set(v___f_970_, 5, v___x_946_);
lean_closure_set(v___f_970_, 6, v_params_947_);
lean_closure_set(v___f_970_, 7, v_self_948_);
lean_closure_set(v___f_970_, 8, v_b_955_);
lean_closure_set(v___f_970_, 9, v___x_968_);
lean_closure_set(v___f_970_, 10, v_a_949_);
lean_closure_set(v___f_970_, 11, v___x_950_);
lean_closure_set(v___f_970_, 12, v_paramInfoOverrides_966_);
lean_closure_set(v___f_970_, 13, v_n_951_);
lean_closure_set(v___f_970_, 14, v_ref_964_);
lean_closure_set(v___f_970_, 15, v___x_952_);
lean_closure_set(v___f_970_, 16, v___x_969_);
v___x_971_ = l_Lean_Expr_isForall(v_b_955_);
lean_dec_ref(v_b_955_);
v___x_972_ = lean_box(v___x_971_);
v___y_973_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_973_, 0, v___x_972_);
lean_closure_set(v___y_973_, 1, v_projName_965_);
lean_closure_set(v___y_973_, 2, v_n_951_);
lean_closure_set(v___y_973_, 3, v_ref_964_);
lean_closure_set(v___y_973_, 4, v___f_970_);
v___x_974_ = l_Lean_isPrivateName(v_projName_965_);
v___x_975_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_973_, v___x_974_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_add(v_a_954_, v___x_977_);
lean_dec(v_a_954_);
v_a_954_ = v___x_978_;
v_b_955_ = v_a_976_;
goto _start;
}
else
{
lean_dec(v_a_954_);
lean_dec(v___x_952_);
lean_dec(v_n_951_);
lean_dec_ref(v___x_950_);
lean_dec_ref(v_a_949_);
lean_dec_ref(v_self_948_);
lean_dec_ref(v_params_947_);
lean_dec(v___x_946_);
lean_dec(v___x_944_);
lean_dec_ref(v___x_943_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_980_ = _args[0];
lean_object* v_projDecls_981_ = _args[1];
lean_object* v___x_982_ = _args[2];
lean_object* v___x_983_ = _args[3];
lean_object* v_instImplicit_984_ = _args[4];
lean_object* v___x_985_ = _args[5];
lean_object* v_params_986_ = _args[6];
lean_object* v_self_987_ = _args[7];
lean_object* v_a_988_ = _args[8];
lean_object* v___x_989_ = _args[9];
lean_object* v_n_990_ = _args[10];
lean_object* v___x_991_ = _args[11];
lean_object* v_a_992_ = _args[12];
lean_object* v_a_993_ = _args[13];
lean_object* v_b_994_ = _args[14];
lean_object* v___y_995_ = _args[15];
lean_object* v___y_996_ = _args[16];
lean_object* v___y_997_ = _args[17];
lean_object* v___y_998_ = _args[18];
lean_object* v___y_999_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1000_; uint8_t v_a_19577__boxed_1001_; lean_object* v_res_1002_; 
v_instImplicit_boxed_1000_ = lean_unbox(v_instImplicit_984_);
v_a_19577__boxed_1001_ = lean_unbox(v_a_992_);
v_res_1002_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_980_, v_projDecls_981_, v___x_982_, v___x_983_, v_instImplicit_boxed_1000_, v___x_985_, v_params_986_, v_self_987_, v_a_988_, v___x_989_, v_n_990_, v___x_991_, v_a_19577__boxed_1001_, v_a_993_, v_b_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_projDecls_981_);
lean_dec(v_upperBound_980_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1003_, lean_object* v_as_1004_, size_t v_sz_1005_, size_t v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_usize_dec_lt(v_i_1006_, v_sz_1005_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_b_1007_);
return v___x_1013_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1014_ = lean_array_uget_borrowed(v_as_1004_, v_i_1006_);
v___x_1015_ = l_Lean_Expr_fvarId_x21(v_a_1014_);
lean_inc(v___x_1015_);
v___x_1016_ = l_Lean_FVarId_getDecl___redArg(v___x_1015_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v_a_1019_; uint8_t v___y_1024_; uint8_t v___x_1027_; uint8_t v___x_1028_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1027_ = l_Lean_LocalDecl_binderInfo(v_a_1017_);
v___x_1028_ = l_Lean_BinderInfo_isInstImplicit(v___x_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1030_ = l_Lean_LocalDecl_type(v_a_1017_);
lean_dec(v_a_1017_);
v___x_1031_ = lean_is_out_param(v___x_1030_);
if (v___x_1031_ == 0)
{
uint8_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = 0;
v___x_1033_ = l_Lean_LocalContext_setBinderInfo(v_b_1007_, v___x_1015_, v___x_1032_);
v_a_1019_ = v___x_1033_;
goto v___jp_1018_;
}
else
{
goto v___jp_1029_;
}
}
else
{
lean_dec(v_a_1017_);
goto v___jp_1029_;
}
v___jp_1018_:
{
size_t v___x_1020_; size_t v___x_1021_; 
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_1006_, v___x_1020_);
v_i_1006_ = v___x_1021_;
v_b_1007_ = v_a_1019_;
goto _start;
}
v___jp_1023_:
{
if (v___y_1024_ == 0)
{
lean_dec(v___x_1015_);
v_a_1019_ = v_b_1007_;
goto v___jp_1018_;
}
else
{
uint8_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = 1;
v___x_1026_ = l_Lean_LocalContext_setBinderInfo(v_b_1007_, v___x_1015_, v___x_1025_);
v_a_1019_ = v___x_1026_;
goto v___jp_1018_;
}
}
v___jp_1029_:
{
if (v___x_1028_ == 0)
{
v___y_1024_ = v___x_1028_;
goto v___jp_1023_;
}
else
{
v___y_1024_ = v_instImplicit_1003_;
goto v___jp_1023_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v___x_1015_);
lean_dec_ref(v_b_1007_);
v_a_1034_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1016_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1016_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1042_, lean_object* v_as_1043_, lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_instImplicit_boxed_1051_; size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_instImplicit_boxed_1051_ = lean_unbox(v_instImplicit_1042_);
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1051_, v_as_1043_, v_sz_boxed_1052_, v_i_boxed_1053_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_as_1043_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1055_, uint8_t v_instImplicit_1056_, lean_object* v_projDecls_1057_, lean_object* v_toConstantVal_1058_, lean_object* v_numParams_1059_, lean_object* v___x_1060_, lean_object* v_n_1061_, lean_object* v_levelParams_1062_, uint8_t v_a_1063_, lean_object* v_ctorType_1064_, lean_object* v_self_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_lctx_1071_; lean_object* v___x_1072_; size_t v_sz_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v_lctx_1071_ = lean_ctor_get(v___y_1066_, 2);
lean_inc_ref(v_self_1065_);
lean_inc_ref(v_params_1055_);
v___x_1072_ = lean_array_push(v_params_1055_, v_self_1065_);
v_sz_1073_ = lean_array_size(v_params_1055_);
v___x_1074_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1071_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1056_, v_params_1055_, v_sz_1073_, v___x_1074_, v_lctx_1071_, v___y_1066_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = lean_array_get_size(v_projDecls_1057_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1077_, v_projDecls_1057_, v_toConstantVal_1058_, v_numParams_1059_, v_instImplicit_1056_, v___x_1060_, v_params_1055_, v_self_1065_, v_a_1076_, v___x_1072_, v_n_1061_, v_levelParams_1062_, v_a_1063_, v___x_1078_, v_ctorType_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1079_, 0);
lean_dec(v_unused_1088_);
v___x_1081_ = v___x_1079_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_dec(v___x_1079_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_box(0);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1079_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1079_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___x_1072_);
lean_dec_ref(v_self_1065_);
lean_dec_ref(v_ctorType_1064_);
lean_dec(v_levelParams_1062_);
lean_dec(v_n_1061_);
lean_dec(v___x_1060_);
lean_dec(v_numParams_1059_);
lean_dec_ref(v_toConstantVal_1058_);
lean_dec_ref(v_params_1055_);
v_a_1097_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1075_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1075_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1105_, lean_object* v_instImplicit_1106_, lean_object* v_projDecls_1107_, lean_object* v_toConstantVal_1108_, lean_object* v_numParams_1109_, lean_object* v___x_1110_, lean_object* v_n_1111_, lean_object* v_levelParams_1112_, lean_object* v_a_1113_, lean_object* v_ctorType_1114_, lean_object* v_self_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_instImplicit_boxed_1121_; uint8_t v_a_19719__boxed_1122_; lean_object* v_res_1123_; 
v_instImplicit_boxed_1121_ = lean_unbox(v_instImplicit_1106_);
v_a_19719__boxed_1122_ = lean_unbox(v_a_1113_);
v_res_1123_ = l_Lean_Meta_mkProjections___lam__0(v_params_1105_, v_instImplicit_boxed_1121_, v_projDecls_1107_, v_toConstantVal_1108_, v_numParams_1109_, v___x_1110_, v_n_1111_, v_levelParams_1112_, v_a_19719__boxed_1122_, v_ctorType_1114_, v_self_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec_ref(v_projDecls_1107_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1133_, lean_object* v_projDecls_1134_, lean_object* v_toConstantVal_1135_, lean_object* v_numParams_1136_, lean_object* v___x_1137_, lean_object* v_n_1138_, lean_object* v_levelParams_1139_, uint8_t v_a_1140_, lean_object* v_params_1141_, lean_object* v_ctorType_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___f_1161_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1159_ = lean_box(v_instImplicit_1133_);
v___x_1160_ = lean_box(v_a_1140_);
lean_inc(v_n_1138_);
lean_inc(v___x_1137_);
lean_inc(v_numParams_1136_);
lean_inc_ref(v_params_1141_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1161_, 0, v_params_1141_);
lean_closure_set(v___f_1161_, 1, v___x_1159_);
lean_closure_set(v___f_1161_, 2, v_projDecls_1134_);
lean_closure_set(v___f_1161_, 3, v_toConstantVal_1135_);
lean_closure_set(v___f_1161_, 4, v_numParams_1136_);
lean_closure_set(v___f_1161_, 5, v___x_1137_);
lean_closure_set(v___f_1161_, 6, v_n_1138_);
lean_closure_set(v___f_1161_, 7, v_levelParams_1139_);
lean_closure_set(v___f_1161_, 8, v___x_1160_);
lean_closure_set(v___f_1161_, 9, v_ctorType_1142_);
v___x_1167_ = lean_array_get_size(v_params_1141_);
v___x_1168_ = lean_nat_dec_eq(v___x_1167_, v_numParams_1136_);
lean_dec(v_numParams_1136_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v___f_1161_);
lean_dec_ref(v_params_1141_);
lean_dec(v___x_1137_);
v___x_1169_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1170_ = l_Lean_MessageData_ofConstName(v_n_1138_, v___x_1168_);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1173_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1174_;
}
else
{
goto v___jp_1162_;
}
v___jp_1148_:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1157_ = 0;
v___x_1158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1156_, v___y_1155_, v___y_1151_, v___y_1149_, v___x_1157_, v___y_1152_, v___y_1150_, v___y_1154_, v___y_1153_);
return v___x_1158_;
}
v___jp_1162_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = l_Lean_Expr_const___override(v_n_1138_, v___x_1137_);
v___x_1164_ = l_Lean_mkAppN(v___x_1163_, v_params_1141_);
lean_dec_ref(v_params_1141_);
if (v_instImplicit_1133_ == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 0;
v___y_1149_ = v___f_1161_;
v___y_1150_ = v___y_1144_;
v___y_1151_ = v___x_1164_;
v___y_1152_ = v___y_1143_;
v___y_1153_ = v___y_1146_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___x_1165_;
goto v___jp_1148_;
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = 3;
v___y_1149_ = v___f_1161_;
v___y_1150_ = v___y_1144_;
v___y_1151_ = v___x_1164_;
v___y_1152_ = v___y_1143_;
v___y_1153_ = v___y_1146_;
v___y_1154_ = v___y_1145_;
v___y_1155_ = v___x_1166_;
goto v___jp_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1175_, lean_object* v_projDecls_1176_, lean_object* v_toConstantVal_1177_, lean_object* v_numParams_1178_, lean_object* v___x_1179_, lean_object* v_n_1180_, lean_object* v_levelParams_1181_, lean_object* v_a_1182_, lean_object* v_params_1183_, lean_object* v_ctorType_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_instImplicit_boxed_1190_; uint8_t v_a_19823__boxed_1191_; lean_object* v_res_1192_; 
v_instImplicit_boxed_1190_ = lean_unbox(v_instImplicit_1175_);
v_a_19823__boxed_1191_ = lean_unbox(v_a_1182_);
v_res_1192_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1190_, v_projDecls_1176_, v_toConstantVal_1177_, v_numParams_1178_, v___x_1179_, v_n_1180_, v_levelParams_1181_, v_a_19823__boxed_1191_, v_params_1183_, v_ctorType_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
if (lean_obj_tag(v_a_1193_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_List_reverse___redArg(v_a_1194_);
return v___x_1195_;
}
else
{
lean_object* v_head_1196_; lean_object* v_tail_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1206_; 
v_head_1196_ = lean_ctor_get(v_a_1193_, 0);
v_tail_1197_ = lean_ctor_get(v_a_1193_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1199_ = v_a_1193_;
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_tail_1197_);
lean_inc(v_head_1196_);
lean_dec(v_a_1193_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_mkLevelParam(v_head_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_a_1194_);
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_a_1194_);
v___x_1203_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v_a_1193_ = v_tail_1197_;
v_a_1194_ = v___x_1203_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_instMonadEIO(lean_box(0));
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_toApplicative_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1281_; 
v___x_1218_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1219_ = l_StateRefT_x27_instMonad___redArg(v___x_1218_);
v_toApplicative_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1219_, 1);
lean_dec(v_unused_1282_);
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1281_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_toApplicative_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1281_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_toFunctor_1224_; lean_object* v_toSeq_1225_; lean_object* v_toSeqLeft_1226_; lean_object* v_toSeqRight_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1279_; 
v_toFunctor_1224_ = lean_ctor_get(v_toApplicative_1220_, 0);
v_toSeq_1225_ = lean_ctor_get(v_toApplicative_1220_, 2);
v_toSeqLeft_1226_ = lean_ctor_get(v_toApplicative_1220_, 3);
v_toSeqRight_1227_ = lean_ctor_get(v_toApplicative_1220_, 4);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_toApplicative_1220_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_toApplicative_1220_, 1);
lean_dec(v_unused_1280_);
v___x_1229_ = v_toApplicative_1220_;
v_isShared_1230_ = v_isSharedCheck_1279_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_toSeqRight_1227_);
lean_inc(v_toSeqLeft_1226_);
lean_inc(v_toSeq_1225_);
lean_inc(v_toFunctor_1224_);
lean_dec(v_toApplicative_1220_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1279_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1240_; 
v___f_1231_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1232_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1224_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toFunctor_1224_);
v___f_1234_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1234_, 0, v_toFunctor_1224_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___f_1233_);
lean_ctor_set(v___x_1235_, 1, v___f_1234_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toSeqRight_1227_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toSeqLeft_1226_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toSeq_1225_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v___f_1236_);
lean_ctor_set(v___x_1229_, 3, v___f_1237_);
lean_ctor_set(v___x_1229_, 2, v___f_1238_);
lean_ctor_set(v___x_1229_, 1, v___f_1231_);
lean_ctor_set(v___x_1229_, 0, v___x_1235_);
v___x_1240_ = v___x_1229_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___f_1231_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v___f_1238_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v___f_1237_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v___f_1236_);
v___x_1240_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v___f_1232_);
lean_ctor_set(v___x_1222_, 0, v___x_1240_);
v___x_1242_ = v___x_1222_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___f_1232_);
v___x_1242_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v_toApplicative_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1275_; 
v___x_1243_ = l_StateRefT_x27_instMonad___redArg(v___x_1242_);
v_toApplicative_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1243_, 1);
lean_dec(v_unused_1276_);
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1275_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_toApplicative_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1275_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_toFunctor_1248_; lean_object* v_toSeq_1249_; lean_object* v_toSeqLeft_1250_; lean_object* v_toSeqRight_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1273_; 
v_toFunctor_1248_ = lean_ctor_get(v_toApplicative_1244_, 0);
v_toSeq_1249_ = lean_ctor_get(v_toApplicative_1244_, 2);
v_toSeqLeft_1250_ = lean_ctor_get(v_toApplicative_1244_, 3);
v_toSeqRight_1251_ = lean_ctor_get(v_toApplicative_1244_, 4);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_toApplicative_1244_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v_toApplicative_1244_, 1);
lean_dec(v_unused_1274_);
v___x_1253_ = v_toApplicative_1244_;
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_toSeqRight_1251_);
lean_inc(v_toSeqLeft_1250_);
lean_inc(v_toSeq_1249_);
lean_inc(v_toFunctor_1248_);
lean_dec(v_toApplicative_1244_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___f_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1264_; 
v___f_1255_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1256_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1248_);
v___f_1257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1257_, 0, v_toFunctor_1248_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toFunctor_1248_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___f_1257_);
lean_ctor_set(v___x_1259_, 1, v___f_1258_);
v___f_1260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1260_, 0, v_toSeqRight_1251_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toSeqLeft_1250_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toSeq_1249_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v___f_1260_);
lean_ctor_set(v___x_1253_, 3, v___f_1261_);
lean_ctor_set(v___x_1253_, 2, v___f_1262_);
lean_ctor_set(v___x_1253_, 1, v___f_1255_);
lean_ctor_set(v___x_1253_, 0, v___x_1259_);
v___x_1264_ = v___x_1253_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___f_1255_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v___f_1262_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___f_1261_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v___f_1260_);
v___x_1264_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___f_1256_);
lean_ctor_set(v___x_1246_, 0, v___x_1264_);
v___x_1266_ = v___x_1246_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___f_1256_);
v___x_1266_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_14652__overap_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l_instInhabitedOfMonad___redArg(v___x_1266_, v___x_1267_);
v___x_14652__overap_1269_ = lean_panic_fn_borrowed(v___x_1268_, v_msg_1212_);
lean_dec(v___x_1268_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1270_ = lean_apply_5(v___x_14652__overap_1269_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, lean_box(0));
return v___x_1270_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1296_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1297_ = lean_unsigned_to_nat(11u);
v___x_1298_ = lean_unsigned_to_nat(122u);
v___x_1299_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1300_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1301_ = l_mkPanicMessageWithDecl(v___x_1300_, v___x_1299_, v___x_1298_, v___x_1297_, v___x_1296_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1316_; lean_object* v_env_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_st_ref_get(v___y_1306_);
v_env_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_ref(v_env_1317_);
lean_dec(v___x_1316_);
v___x_1318_ = 0;
lean_inc(v_constName_1302_);
v___x_1319_ = l_Lean_Environment_findAsync_x3f(v_env_1317_, v_constName_1302_, v___x_1318_);
if (lean_obj_tag(v___x_1319_) == 1)
{
lean_object* v_val_1320_; uint8_t v_kind_1321_; 
v_val_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1320_);
lean_dec_ref(v___x_1319_);
v_kind_1321_ = lean_ctor_get_uint8(v_val_1320_, sizeof(void*)*3);
if (v_kind_1321_ == 6)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1320_);
if (lean_obj_tag(v___x_1322_) == 6)
{
lean_object* v_val_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_constName_1302_);
v_val_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_val_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 0);
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_val_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v___x_1322_);
v___x_1331_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1332_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1331_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
if (lean_obj_tag(v_a_1333_) == 0)
{
lean_del_object(v___x_1335_);
goto v___jp_1308_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1339_; 
lean_dec(v_constName_1302_);
v_val_1337_ = lean_ctor_get(v_a_1333_, 0);
lean_inc(v_val_1337_);
lean_dec_ref(v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_val_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_constName_1302_);
v_a_1342_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1332_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_dec(v_val_1320_);
goto v___jp_1308_;
}
}
else
{
lean_dec(v___x_1319_);
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1309_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1310_ = 0;
v___x_1311_ = l_Lean_MessageData_ofConstName(v_constName_1302_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1309_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1314_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_env_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_st_ref_get(v___y_1364_);
v_env_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_ref(v_env_1367_);
lean_dec(v___x_1366_);
lean_inc(v_constName_1360_);
v___x_1368_ = l_Lean_isInductiveCore_x3f(v_env_1367_, v_constName_1360_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1369_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1370_ = 0;
v___x_1371_ = l_Lean_MessageData_ofConstName(v_constName_1360_, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1369_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1374_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_constName_1360_);
v_val_1376_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1368_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_val_1376_);
lean_dec(v___x_1368_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 0);
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_val_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1390_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1393_ = l_Lean_stringToMessageData(v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1397_, lean_object* v___x_1398_, uint8_t v_instImplicit_1399_, lean_object* v_projDecls_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
lean_inc(v_n_1397_);
v___x_1406_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1397_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1448_ = l_Lean_InductiveVal_numCtors(v_a_1407_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_dec_eq(v___x_1448_, v___x_1449_);
lean_dec(v___x_1448_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_a_1407_);
lean_dec_ref(v_projDecls_1400_);
v___x_1451_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1452_ = l_Lean_MessageData_ofConstName(v_n_1397_, v___x_1450_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1455_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1456_;
}
else
{
v___y_1409_ = v___y_1401_;
v___y_1410_ = v___y_1402_;
v___y_1411_ = v___y_1403_;
v___y_1412_ = v___y_1404_;
goto v___jp_1408_;
}
v___jp_1408_:
{
lean_object* v_toConstantVal_1413_; lean_object* v_numParams_1414_; lean_object* v_ctors_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_toConstantVal_1413_ = lean_ctor_get(v_a_1407_, 0);
lean_inc_ref(v_toConstantVal_1413_);
v_numParams_1414_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_numParams_1414_);
v_ctors_1415_ = lean_ctor_get(v_a_1407_, 4);
lean_inc(v_ctors_1415_);
lean_dec(v_a_1407_);
v___x_1416_ = l_List_head_x21___redArg(v___x_1398_, v_ctors_1415_);
lean_dec(v_ctors_1415_);
v___x_1417_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1416_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v_levelParams_1419_; lean_object* v_type_1420_; lean_object* v___x_1421_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v_levelParams_1419_ = lean_ctor_get(v_toConstantVal_1413_, 1);
lean_inc(v_levelParams_1419_);
v_type_1420_ = lean_ctor_get(v_toConstantVal_1413_, 2);
lean_inc_ref(v_type_1420_);
lean_dec_ref(v_toConstantVal_1413_);
v___x_1421_ = l_Lean_Meta_isPropFormerType(v_type_1420_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_toConstantVal_1422_; lean_object* v_a_1423_; lean_object* v_type_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; lean_object* v___x_1431_; 
v_toConstantVal_1422_ = lean_ctor_get(v_a_1418_, 0);
lean_inc_ref(v_toConstantVal_1422_);
lean_dec(v_a_1418_);
v_a_1423_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1421_);
v_type_1424_ = lean_ctor_get(v_toConstantVal_1422_, 2);
lean_inc_ref(v_type_1424_);
v___x_1425_ = lean_box(0);
lean_inc(v_levelParams_1419_);
v___x_1426_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1419_, v___x_1425_);
v___x_1427_ = lean_box(v_instImplicit_1399_);
lean_inc(v_numParams_1414_);
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1428_, 0, v___x_1427_);
lean_closure_set(v___f_1428_, 1, v_projDecls_1400_);
lean_closure_set(v___f_1428_, 2, v_toConstantVal_1422_);
lean_closure_set(v___f_1428_, 3, v_numParams_1414_);
lean_closure_set(v___f_1428_, 4, v___x_1426_);
lean_closure_set(v___f_1428_, 5, v_n_1397_);
lean_closure_set(v___f_1428_, 6, v_levelParams_1419_);
lean_closure_set(v___f_1428_, 7, v_a_1423_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_numParams_1414_);
v___x_1430_ = 0;
v___x_1431_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1424_, v___x_1429_, v___f_1428_, v___x_1430_, v___x_1430_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1431_;
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_levelParams_1419_);
lean_dec(v_a_1418_);
lean_dec(v_numParams_1414_);
lean_dec_ref(v_projDecls_1400_);
lean_dec(v_n_1397_);
v_a_1432_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1421_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1421_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_numParams_1414_);
lean_dec_ref(v_toConstantVal_1413_);
lean_dec_ref(v_projDecls_1400_);
lean_dec(v_n_1397_);
v_a_1440_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1417_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1417_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_projDecls_1400_);
lean_dec(v_n_1397_);
v_a_1457_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1406_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1406_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1465_, lean_object* v___x_1466_, lean_object* v_instImplicit_1467_, lean_object* v_projDecls_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_instImplicit_boxed_1474_; lean_object* v_res_1475_; 
v_instImplicit_boxed_1474_ = lean_unbox(v_instImplicit_1467_);
v_res_1475_ = l_Lean_Meta_mkProjections___lam__2(v_n_1465_, v___x_1466_, v_instImplicit_boxed_1474_, v_projDecls_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___x_1466_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_unsigned_to_nat(32u);
v___x_1480_ = lean_mk_empty_array_with_capacity(v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = ((size_t)5ULL);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_unsigned_to_nat(32u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1487_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
lean_ctor_set(v___x_1487_, 2, v___x_1483_);
lean_ctor_set(v___x_1487_, 3, v___x_1483_);
lean_ctor_set_usize(v___x_1487_, 4, v___x_1482_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = lean_box(1);
v___x_1489_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1490_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___x_1489_);
lean_ctor_set(v___x_1491_, 2, v___x_1488_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1494_, lean_object* v_projDecls_1495_, uint8_t v_instImplicit_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_box(v_instImplicit_1496_);
v___f_1504_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1504_, 0, v_n_1494_);
lean_closure_set(v___f_1504_, 1, v___x_1502_);
lean_closure_set(v___f_1504_, 2, v___x_1503_);
lean_closure_set(v___f_1504_, 3, v_projDecls_1495_);
v___x_1505_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1506_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1507_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1505_, v___x_1506_, v___f_1504_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1508_, lean_object* v_projDecls_1509_, lean_object* v_instImplicit_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
uint8_t v_instImplicit_boxed_1516_; lean_object* v_res_1517_; 
v_instImplicit_boxed_1516_ = lean_unbox(v_instImplicit_1510_);
v_res_1517_ = l_Lean_Meta_mkProjections(v_n_1508_, v_projDecls_1509_, v_instImplicit_boxed_1516_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1518_, lean_object* v_as_1519_, size_t v_sz_1520_, size_t v_i_1521_, lean_object* v_b_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1518_, v_as_1519_, v_sz_1520_, v_i_1521_, v_b_1522_, v___y_1523_, v___y_1525_, v___y_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1529_, lean_object* v_as_1530_, lean_object* v_sz_1531_, lean_object* v_i_1532_, lean_object* v_b_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_instImplicit_boxed_1539_; size_t v_sz_boxed_1540_; size_t v_i_boxed_1541_; lean_object* v_res_1542_; 
v_instImplicit_boxed_1539_ = lean_unbox(v_instImplicit_1529_);
v_sz_boxed_1540_ = lean_unbox_usize(v_sz_1531_);
lean_dec(v_sz_1531_);
v_i_boxed_1541_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1539_, v_as_1530_, v_sz_boxed_1540_, v_i_boxed_1541_, v_b_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v_as_1530_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1543_, uint8_t v_s_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1543_, v_s_1544_, v___y_1546_, v___y_1548_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1551_, lean_object* v_s_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_s_boxed_1558_; lean_object* v_res_1559_; 
v_s_boxed_1558_ = lean_unbox(v_s_1552_);
v_res_1559_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1551_, v_s_boxed_1558_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1560_, lean_object* v_ref_1561_, lean_object* v_msg_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1561_, v_msg_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_ref_1570_, lean_object* v_msg_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1569_, v_ref_1570_, v_msg_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_ref_1570_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1578_, lean_object* v_x_1579_, uint8_t v_isExporting_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1579_, v_isExporting_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1587_, lean_object* v_x_1588_, lean_object* v_isExporting_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
uint8_t v_isExporting_boxed_1595_; lean_object* v_res_1596_; 
v_isExporting_boxed_1595_ = lean_unbox(v_isExporting_1589_);
v_res_1596_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1587_, v_x_1588_, v_isExporting_boxed_1595_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1597_, lean_object* v_x_1598_, uint8_t v_when_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1598_, v_when_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_x_1607_, lean_object* v_when_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
uint8_t v_when_boxed_1614_; lean_object* v_res_1615_; 
v_when_boxed_1614_ = lean_unbox(v_when_1608_);
v_res_1615_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1606_, v_x_1607_, v_when_boxed_1614_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1616_, lean_object* v_projDecls_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, uint8_t v_instImplicit_1620_, lean_object* v___x_1621_, lean_object* v_params_1622_, lean_object* v_self_1623_, lean_object* v_a_1624_, lean_object* v___x_1625_, lean_object* v_n_1626_, lean_object* v___x_1627_, uint8_t v_a_1628_, lean_object* v_inst_1629_, lean_object* v_R_1630_, lean_object* v_a_1631_, lean_object* v_b_1632_, lean_object* v_c_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1616_, v_projDecls_1617_, v___x_1618_, v___x_1619_, v_instImplicit_1620_, v___x_1621_, v_params_1622_, v_self_1623_, v_a_1624_, v___x_1625_, v_n_1626_, v___x_1627_, v_a_1628_, v_a_1631_, v_b_1632_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1640_ = _args[0];
lean_object* v_projDecls_1641_ = _args[1];
lean_object* v___x_1642_ = _args[2];
lean_object* v___x_1643_ = _args[3];
lean_object* v_instImplicit_1644_ = _args[4];
lean_object* v___x_1645_ = _args[5];
lean_object* v_params_1646_ = _args[6];
lean_object* v_self_1647_ = _args[7];
lean_object* v_a_1648_ = _args[8];
lean_object* v___x_1649_ = _args[9];
lean_object* v_n_1650_ = _args[10];
lean_object* v___x_1651_ = _args[11];
lean_object* v_a_1652_ = _args[12];
lean_object* v_inst_1653_ = _args[13];
lean_object* v_R_1654_ = _args[14];
lean_object* v_a_1655_ = _args[15];
lean_object* v_b_1656_ = _args[16];
lean_object* v_c_1657_ = _args[17];
lean_object* v___y_1658_ = _args[18];
lean_object* v___y_1659_ = _args[19];
lean_object* v___y_1660_ = _args[20];
lean_object* v___y_1661_ = _args[21];
lean_object* v___y_1662_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1663_; uint8_t v_a_20576__boxed_1664_; lean_object* v_res_1665_; 
v_instImplicit_boxed_1663_ = lean_unbox(v_instImplicit_1644_);
v_a_20576__boxed_1664_ = lean_unbox(v_a_1652_);
v_res_1665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1640_, v_projDecls_1641_, v___x_1642_, v___x_1643_, v_instImplicit_boxed_1663_, v___x_1645_, v_params_1646_, v_self_1647_, v_a_1648_, v___x_1649_, v_n_1650_, v___x_1651_, v_a_20576__boxed_1664_, v_inst_1653_, v_R_1654_, v_a_1655_, v_b_1656_, v_c_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v_projDecls_1641_);
lean_dec(v_upperBound_1640_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1666_, uint8_t v_allowLevelAssignments_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1667_, v_k_1666_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1673_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1673_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1690_, lean_object* v_allowLevelAssignments_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1697_; lean_object* v_res_1698_; 
v_allowLevelAssignments_boxed_1697_ = lean_unbox(v_allowLevelAssignments_1691_);
v_res_1698_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1690_, v_allowLevelAssignments_boxed_1697_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1699_, lean_object* v_k_1700_, uint8_t v_allowLevelAssignments_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1700_, v_allowLevelAssignments_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_k_1709_, lean_object* v_allowLevelAssignments_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1716_; lean_object* v_res_1717_; 
v_allowLevelAssignments_boxed_1716_ = lean_unbox(v_allowLevelAssignments_1710_);
v_res_1717_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1708_, v_k_1709_, v_allowLevelAssignments_boxed_1716_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_b_1721_);
return v___x_1728_;
}
else
{
lean_object* v_snd_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1784_; 
v_snd_1729_ = lean_ctor_get(v_b_1721_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_b_1721_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_b_1721_, 0);
lean_dec(v_unused_1785_);
v___x_1731_ = v_b_1721_;
v_isShared_1732_ = v_isSharedCheck_1784_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_snd_1729_);
lean_dec(v_b_1721_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1784_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_array_1733_; lean_object* v_start_1734_; lean_object* v_stop_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_array_1733_ = lean_ctor_get(v_snd_1729_, 0);
v_start_1734_ = lean_ctor_get(v_snd_1729_, 1);
v_stop_1735_ = lean_ctor_get(v_snd_1729_, 2);
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_nat_dec_lt(v_start_1734_, v_stop_1735_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1739_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1739_ = v___x_1731_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_snd_1729_);
v___x_1739_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
else
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1780_; 
lean_inc(v_stop_1735_);
lean_inc(v_start_1734_);
lean_inc_ref(v_array_1733_);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_snd_1729_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; 
v_unused_1781_ = lean_ctor_get(v_snd_1729_, 2);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_snd_1729_, 1);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v_snd_1729_, 0);
lean_dec(v_unused_1783_);
v___x_1743_ = v_snd_1729_;
v_isShared_1744_ = v_isSharedCheck_1780_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v_snd_1729_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1780_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_a_1745_ = lean_array_uget_borrowed(v_as_1718_, v_i_1720_);
v___x_1746_ = lean_array_fget_borrowed(v_array_1733_, v_start_1734_);
lean_inc(v___x_1746_);
lean_inc(v_a_1745_);
v___x_1747_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1745_, v___x_1746_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1771_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1771_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_start_1734_, v___x_1752_);
lean_dec(v_start_1734_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v___x_1753_);
v___x_1755_ = v___x_1743_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_array_1733_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_stop_1735_);
v___x_1755_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_unbox(v_a_1748_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_a_1748_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1755_);
lean_ctor_set(v___x_1731_, 0, v___x_1757_);
v___x_1759_ = v___x_1731_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v___x_1755_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1759_);
v___x_1761_ = v___x_1750_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1750_);
lean_dec(v_a_1748_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1755_);
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1765_ = v___x_1731_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1755_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
size_t v___x_1766_; size_t v___x_1767_; 
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1720_, v___x_1766_);
v_i_1720_ = v___x_1767_;
v_b_1721_ = v___x_1765_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1743_);
lean_dec(v_stop_1735_);
lean_dec(v_start_1734_);
lean_dec_ref(v_array_1733_);
lean_del_object(v___x_1731_);
v_a_1772_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1747_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1747_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
size_t v_sz_boxed_1795_; size_t v_i_boxed_1796_; lean_object* v_res_1797_; 
v_sz_boxed_1795_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1796_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1786_, v_sz_boxed_1795_, v_i_boxed_1796_, v_b_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_as_1786_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1798_, lean_object* v_params2_1799_, lean_object* v___x_1800_, lean_object* v_params1_1801_, uint8_t v___x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
if (v___x_1798_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___x_1800_);
lean_dec_ref(v_params2_1799_);
v___x_1808_ = lean_box(v___x_1798_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; size_t v_sz_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = l_Array_toSubarray___redArg(v_params2_1799_, v___x_1810_, v___x_1800_);
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
v_sz_1814_ = lean_array_size(v_params1_1801_);
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1801_, v_sz_1814_, v___x_1815_, v___x_1813_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1830_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1830_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_fst_1821_; 
v_fst_1821_ = lean_ctor_get(v_a_1817_, 0);
lean_inc(v_fst_1821_);
lean_dec(v_a_1817_);
if (lean_obj_tag(v_fst_1821_) == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_box(v___x_1802_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
else
{
lean_object* v_val_1826_; lean_object* v___x_1828_; 
v_val_1826_ = lean_ctor_get(v_fst_1821_, 0);
lean_inc(v_val_1826_);
lean_dec_ref(v_fst_1821_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_val_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_val_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
v_a_1831_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1816_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1816_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1839_, lean_object* v_params2_1840_, lean_object* v___x_1841_, lean_object* v_params1_1842_, lean_object* v___x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v___x_2097__boxed_1849_; uint8_t v___x_2099__boxed_1850_; lean_object* v_res_1851_; 
v___x_2097__boxed_1849_ = lean_unbox(v___x_1839_);
v___x_2099__boxed_1850_ = lean_unbox(v___x_1843_);
v_res_1851_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2097__boxed_1849_, v_params2_1840_, v___x_1841_, v_params1_1842_, v___x_2099__boxed_1850_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v_params1_1842_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1852_, lean_object* v_params2_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___y_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; 
v___x_1859_ = lean_array_get_size(v_params1_1852_);
v___x_1860_ = lean_array_get_size(v_params2_1853_);
v___x_1861_ = lean_nat_dec_eq(v___x_1859_, v___x_1860_);
v___x_1862_ = 1;
v___x_1863_ = lean_box(v___x_1861_);
v___x_1864_ = lean_box(v___x_1862_);
v___y_1865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1865_, 0, v___x_1863_);
lean_closure_set(v___y_1865_, 1, v_params2_1853_);
lean_closure_set(v___y_1865_, 2, v___x_1860_);
lean_closure_set(v___y_1865_, 3, v_params1_1852_);
lean_closure_set(v___y_1865_, 4, v___x_1864_);
v___x_1866_ = 0;
v___x_1867_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1865_, v___x_1866_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1868_, lean_object* v_params2_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1868_, v_params2_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; lean_object* v_env_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_st_ref_get(v___y_1877_);
v_env_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_ref(v_env_1880_);
lean_dec(v___x_1879_);
v___x_1881_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1880_, v_declName_1876_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1883_, v___y_1884_);
lean_dec(v___y_1884_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1887_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1901_; lean_object* v_dummy_1902_; 
v___x_1901_ = lean_box(0);
v_dummy_1902_ = l_Lean_Expr_sort___override(v___x_1901_);
return v_dummy_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1903_, lean_object* v_induct_1904_, lean_object* v_params_1905_, lean_object* v_idx_1906_, lean_object* v_e_1907_, lean_object* v_x_x3f_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
if (lean_obj_tag(v_e_1907_) == 11)
{
lean_object* v_typeName_1920_; lean_object* v_idx_1921_; lean_object* v_struct_1922_; uint8_t v___y_1970_; uint8_t v___x_1973_; 
v_typeName_1920_ = lean_ctor_get(v_e_1907_, 0);
v_idx_1921_ = lean_ctor_get(v_e_1907_, 1);
v_struct_1922_ = lean_ctor_get(v_e_1907_, 2);
lean_inc_ref(v_struct_1922_);
v___x_1973_ = lean_nat_dec_eq(v_idx_1921_, v_idx_1906_);
if (v___x_1973_ == 0)
{
v___y_1970_ = v___x_1973_;
goto v___jp_1969_;
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_name_eq(v_induct_1904_, v_typeName_1920_);
v___y_1970_ = v___x_1974_;
goto v___jp_1969_;
}
v___jp_1923_:
{
lean_object* v___x_1924_; 
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
v___x_1924_ = lean_infer_type(v_e_1907_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
lean_inc(v_a_1912_);
lean_inc_ref(v_a_1911_);
lean_inc(v_a_1910_);
lean_inc_ref(v_a_1909_);
v___x_1926_ = lean_whnf(v_a_1925_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v_dummy_1928_; lean_object* v_nargs_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
v_dummy_1928_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1929_ = l_Lean_Expr_getAppNumArgs(v_a_1927_);
lean_inc(v_nargs_1929_);
v___x_1930_ = lean_mk_array(v_nargs_1929_, v_dummy_1928_);
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_sub(v_nargs_1929_, v___x_1931_);
lean_dec(v_nargs_1929_);
v___x_1933_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1927_, v___x_1930_, v___x_1932_);
v___x_1934_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1905_, v___x_1933_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1944_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
if (v___x_1939_ == 0)
{
lean_del_object(v___x_1937_);
lean_dec_ref(v_struct_1922_);
goto v___jp_1914_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_struct_1922_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_struct_1922_);
v_a_1945_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1934_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1934_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_struct_1922_);
lean_dec_ref(v_params_1905_);
v_a_1953_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1926_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1926_);
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
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_struct_1922_);
lean_dec_ref(v_params_1905_);
v_a_1961_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1924_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1924_);
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
if (v___y_1970_ == 0)
{
lean_dec_ref(v_struct_1922_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1914_;
}
else
{
if (lean_obj_tag(v_x_x3f_1908_) == 0)
{
goto v___jp_1923_;
}
else
{
lean_object* v_val_1971_; uint8_t v___x_1972_; 
v_val_1971_ = lean_ctor_get(v_x_x3f_1908_, 0);
v___x_1972_ = lean_expr_eqv(v_val_1971_, v_struct_1922_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_struct_1922_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1914_;
}
else
{
goto v___jp_1923_;
}
}
}
}
}
else
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Expr_getAppFn(v_e_1907_);
if (lean_obj_tag(v___x_1975_) == 4)
{
lean_object* v_declName_1976_; lean_object* v___x_1977_; lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2027_; 
v_declName_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_declName_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1976_, v_a_1912_);
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2027_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2027_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___y_1983_; lean_object* v___y_1984_; 
if (lean_obj_tag(v_a_1978_) == 1)
{
lean_object* v_val_2012_; lean_object* v_ctorName_2013_; lean_object* v_numParams_2014_; lean_object* v_i_2015_; uint8_t v___y_2017_; uint8_t v___x_2025_; 
v_val_2012_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_val_2012_);
lean_dec_ref(v_a_1978_);
v_ctorName_2013_ = lean_ctor_get(v_val_2012_, 0);
lean_inc(v_ctorName_2013_);
v_numParams_2014_ = lean_ctor_get(v_val_2012_, 1);
lean_inc(v_numParams_2014_);
v_i_2015_ = lean_ctor_get(v_val_2012_, 2);
lean_inc(v_i_2015_);
lean_dec(v_val_2012_);
v___x_2025_ = lean_name_eq(v_ctorName_2013_, v_ctor_1903_);
lean_dec(v_ctorName_2013_);
if (v___x_2025_ == 0)
{
lean_dec(v_i_2015_);
v___y_2017_ = v___x_2025_;
goto v___jp_2016_;
}
else
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_nat_dec_eq(v_i_2015_, v_idx_1906_);
lean_dec(v_i_2015_);
v___y_2017_ = v___x_2026_;
goto v___jp_2016_;
}
v___jp_2016_:
{
if (v___y_2017_ == 0)
{
lean_dec(v_numParams_2014_);
lean_del_object(v___x_1980_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1917_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2018_ = l_Lean_Expr_getAppNumArgs(v_e_1907_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_add(v_numParams_2014_, v___x_2019_);
lean_dec(v_numParams_2014_);
v___x_2021_ = lean_nat_dec_eq(v___x_2018_, v___x_2020_);
lean_dec(v___x_2020_);
lean_dec(v___x_2018_);
if (v___x_2021_ == 0)
{
lean_del_object(v___x_1980_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1917_;
}
else
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Expr_appArg_x21(v_e_1907_);
if (lean_obj_tag(v_x_x3f_1908_) == 0)
{
v___y_1983_ = v___x_2022_;
v___y_1984_ = v___x_2019_;
goto v___jp_1982_;
}
else
{
lean_object* v_val_2023_; uint8_t v___x_2024_; 
v_val_2023_ = lean_ctor_get(v_x_x3f_1908_, 0);
v___x_2024_ = lean_expr_eqv(v_val_2023_, v___x_2022_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v___x_2022_);
lean_del_object(v___x_1980_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1917_;
}
else
{
v___y_1983_ = v___x_2022_;
v___y_1984_ = v___x_2019_;
goto v___jp_1982_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1980_);
lean_dec(v_a_1978_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1917_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; lean_object* v_dummy_1986_; lean_object* v_nargs_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1985_ = l_Lean_Expr_appFn_x21(v_e_1907_);
lean_dec_ref(v_e_1907_);
v_dummy_1986_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1987_ = l_Lean_Expr_getAppNumArgs(v___x_1985_);
lean_inc(v_nargs_1987_);
v___x_1988_ = lean_mk_array(v_nargs_1987_, v_dummy_1986_);
v___x_1989_ = lean_nat_sub(v_nargs_1987_, v___y_1984_);
lean_dec(v_nargs_1987_);
v___x_1990_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1985_, v___x_1988_, v___x_1989_);
v___x_1991_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1905_, v___x_1990_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2003_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_unbox(v_a_1992_);
lean_dec(v_a_1992_);
if (v___x_1996_ == 0)
{
lean_del_object(v___x_1994_);
lean_dec_ref(v___y_1983_);
lean_del_object(v___x_1980_);
goto v___jp_1917_;
}
else
{
lean_object* v___x_1998_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 0, v___y_1983_);
v___x_1998_ = v___x_1980_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___y_1983_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1998_);
v___x_2000_ = v___x_1994_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v___y_1983_);
lean_del_object(v___x_1980_);
v_a_2004_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1991_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1991_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_params_1905_);
goto v___jp_1917_;
}
}
v___jp_1914_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
v___jp_1917_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
return v___x_1919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2028_, lean_object* v_induct_2029_, lean_object* v_params_2030_, lean_object* v_idx_2031_, lean_object* v_e_2032_, lean_object* v_x_x3f_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2028_, v_induct_2029_, v_params_2030_, v_idx_2031_, v_e_2032_, v_x_x3f_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_x_x3f_2033_);
lean_dec(v_idx_2031_);
lean_dec(v_induct_2029_);
lean_dec(v_ctor_2028_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_env_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2046_ = lean_st_ref_get(v___y_2044_);
v_env_2050_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2050_);
lean_dec(v___x_2046_);
v___x_2051_ = 0;
v___x_2052_ = l_Lean_Environment_findAsync_x3f(v_env_2050_, v_constName_2040_, v___x_2051_);
if (lean_obj_tag(v___x_2052_) == 1)
{
lean_object* v_val_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2072_; 
v_val_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2072_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_val_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2072_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
uint8_t v_kind_2057_; 
v_kind_2057_ = lean_ctor_get_uint8(v_val_2053_, sizeof(void*)*3);
if (v_kind_2057_ == 6)
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2053_);
if (lean_obj_tag(v___x_2058_) == 6)
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_val_2059_);
v___x_2064_ = v___x_2055_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2059_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec_ref(v___x_2058_);
lean_del_object(v___x_2055_);
v___x_2070_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2071_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2070_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
return v___x_2071_;
}
}
else
{
lean_del_object(v___x_2055_);
lean_dec(v_val_2053_);
goto v___jp_2047_;
}
}
}
else
{
lean_dec(v___x_2052_);
goto v___jp_2047_;
}
v___jp_2047_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v_declName_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_a_2094_, lean_object* v_val_2095_, lean_object* v_a_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_lt(v_a_2096_, v_upperBound_2088_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___x_2093_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_b_2097_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec_ref(v_b_2097_);
v___x_2105_ = l_Lean_instInhabitedExpr;
v___x_2106_ = lean_nat_add(v___x_2089_, v_a_2096_);
v___x_2107_ = lean_array_get_borrowed(v___x_2105_, v___x_2090_, v___x_2106_);
lean_dec(v___x_2106_);
lean_inc(v___x_2107_);
lean_inc_ref(v___x_2093_);
v___x_2108_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2091_, v___x_2092_, v___x_2093_, v_a_2096_, v___x_2107_, v_a_2094_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2127_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2127_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2127_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
if (lean_obj_tag(v_a_2109_) == 1)
{
lean_object* v_val_2113_; uint8_t v___x_2114_; 
v_val_2113_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_val_2113_);
lean_dec_ref(v_a_2109_);
v___x_2114_ = lean_expr_eqv(v_val_2113_, v_val_2095_);
lean_dec(v_val_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___x_2093_);
v___x_2115_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2117_ = v___x_2111_;
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
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_del_object(v___x_2111_);
v___x_2119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = lean_nat_add(v_a_2096_, v___x_2120_);
lean_dec(v_a_2096_);
v_a_2096_ = v___x_2121_;
v_b_2097_ = v___x_2119_;
goto _start;
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_a_2109_);
lean_dec(v_a_2096_);
lean_dec_ref(v___x_2093_);
v___x_2123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2123_);
v___x_2125_ = v___x_2111_;
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
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_a_2096_);
lean_dec_ref(v___x_2093_);
v_a_2128_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2108_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2108_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2136_, lean_object* v___x_2137_, lean_object* v___x_2138_, lean_object* v_declName_2139_, lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v_a_2142_, lean_object* v_val_2143_, lean_object* v_a_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2136_, v___x_2137_, v___x_2138_, v_declName_2139_, v___x_2140_, v___x_2141_, v_a_2142_, v_val_2143_, v_a_2144_, v_b_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec_ref(v_val_2143_);
lean_dec(v_a_2142_);
lean_dec(v___x_2140_);
lean_dec(v_declName_2139_);
lean_dec_ref(v___x_2138_);
lean_dec(v___x_2137_);
lean_dec(v_upperBound_2136_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2152_, lean_object* v_p_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Expr_getAppFn(v_e_2152_);
if (lean_obj_tag(v___x_2159_) == 4)
{
lean_object* v_declName_2160_; lean_object* v___x_2161_; 
v_declName_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc_n(v_declName_2160_, 2);
lean_dec_ref(v___x_2159_);
v___x_2161_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2160_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2234_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2234_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2234_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
if (lean_obj_tag(v_a_2162_) == 1)
{
lean_object* v_val_2166_; lean_object* v_induct_2167_; lean_object* v_numParams_2168_; lean_object* v_numFields_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_val_2166_ = lean_ctor_get(v_a_2162_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_a_2162_);
v_induct_2167_ = lean_ctor_get(v_val_2166_, 1);
lean_inc_n(v_induct_2167_, 2);
v_numParams_2168_ = lean_ctor_get(v_val_2166_, 3);
lean_inc(v_numParams_2168_);
v_numFields_2169_ = lean_ctor_get(v_val_2166_, 4);
lean_inc(v_numFields_2169_);
lean_dec(v_val_2166_);
v___x_2170_ = lean_apply_1(v_p_2153_, v_induct_2167_);
v___x_2171_ = lean_unbox(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2160_);
lean_dec_ref(v_e_2152_);
v___x_2172_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2172_);
v___x_2174_ = v___x_2164_;
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
lean_object* v___x_2176_; uint8_t v___y_2178_; uint8_t v___x_2226_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_nat_dec_lt(v___x_2176_, v_numFields_2169_);
if (v___x_2226_ == 0)
{
v___y_2178_ = v___x_2226_;
goto v___jp_2177_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2227_ = l_Lean_Expr_getAppNumArgs(v_e_2152_);
v___x_2228_ = lean_nat_add(v_numParams_2168_, v_numFields_2169_);
v___x_2229_ = lean_nat_dec_eq(v___x_2227_, v___x_2228_);
lean_dec(v___x_2228_);
lean_dec(v___x_2227_);
v___y_2178_ = v___x_2229_;
goto v___jp_2177_;
}
v___jp_2177_:
{
if (v___y_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2160_);
lean_dec_ref(v_e_2152_);
v___x_2179_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2179_);
v___x_2181_ = v___x_2164_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v_dummy_2183_; lean_object* v_nargs_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_del_object(v___x_2164_);
v_dummy_2183_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2184_ = l_Lean_Expr_getAppNumArgs(v_e_2152_);
lean_inc(v_nargs_2184_);
v___x_2185_ = lean_mk_array(v_nargs_2184_, v_dummy_2183_);
v___x_2186_ = lean_unsigned_to_nat(1u);
v___x_2187_ = lean_nat_sub(v_nargs_2184_, v___x_2186_);
lean_dec(v_nargs_2184_);
v___x_2188_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2152_, v___x_2185_, v___x_2187_);
lean_inc(v_numParams_2168_);
v___x_2189_ = l_Array_extract___redArg(v___x_2188_, v___x_2176_, v_numParams_2168_);
v___x_2190_ = l_Lean_instInhabitedExpr;
v___x_2191_ = lean_array_get(v___x_2190_, v___x_2188_, v_numParams_2168_);
v___x_2192_ = lean_box(0);
lean_inc_ref(v___x_2189_);
v___x_2193_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2160_, v_induct_2167_, v___x_2189_, v___x_2176_, v___x_2191_, v___x_2192_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2225_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2225_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2225_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
if (lean_obj_tag(v_a_2194_) == 1)
{
lean_object* v_val_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_del_object(v___x_2196_);
v_val_2198_ = lean_ctor_get(v_a_2194_, 0);
v___x_2199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2169_, v_numParams_2168_, v___x_2188_, v_declName_2160_, v_induct_2167_, v___x_2189_, v_a_2194_, v_val_2198_, v___x_2186_, v___x_2199_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2160_);
lean_dec_ref(v___x_2188_);
lean_dec(v_numParams_2168_);
lean_dec(v_numFields_2169_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2213_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_fst_2205_; 
v_fst_2205_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_fst_2205_);
lean_dec(v_a_2201_);
if (lean_obj_tag(v_fst_2205_) == 0)
{
lean_object* v___x_2207_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_a_2194_);
v___x_2207_ = v___x_2203_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2194_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; 
lean_dec_ref(v_a_2194_);
v_val_2209_ = lean_ctor_get(v_fst_2205_, 0);
lean_inc(v_val_2209_);
lean_dec_ref(v_fst_2205_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_val_2209_);
v___x_2211_ = v___x_2203_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_val_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v_a_2194_);
v_a_2214_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2200_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2200_);
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
lean_object* v___x_2223_; 
lean_dec(v_a_2194_);
lean_dec_ref(v___x_2189_);
lean_dec_ref(v___x_2188_);
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2160_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2192_);
v___x_2223_ = v___x_2196_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2192_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_dec_ref(v___x_2189_);
lean_dec_ref(v___x_2188_);
lean_dec(v_numFields_2169_);
lean_dec(v_numParams_2168_);
lean_dec(v_induct_2167_);
lean_dec(v_declName_2160_);
return v___x_2193_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
lean_dec(v_a_2162_);
lean_dec(v_declName_2160_);
lean_dec_ref(v_p_2153_);
lean_dec_ref(v_e_2152_);
v___x_2230_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2230_);
v___x_2232_ = v___x_2164_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
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
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_declName_2160_);
lean_dec_ref(v_p_2153_);
lean_dec_ref(v_e_2152_);
v_a_2235_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2161_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2161_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v___x_2159_);
lean_dec_ref(v_p_2153_);
lean_dec_ref(v_e_2152_);
v___x_2243_ = lean_box(0);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2245_, lean_object* v_p_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_etaStruct_x3f(v_e_2245_, v_p_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v_declName_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v_a_2259_, lean_object* v_val_2260_, lean_object* v_inst_2261_, lean_object* v_R_2262_, lean_object* v_a_2263_, lean_object* v_b_2264_, lean_object* v_c_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2253_, v___x_2254_, v___x_2255_, v_declName_2256_, v___x_2257_, v___x_2258_, v_a_2259_, v_val_2260_, v_a_2263_, v_b_2264_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2272_ = _args[0];
lean_object* v___x_2273_ = _args[1];
lean_object* v___x_2274_ = _args[2];
lean_object* v_declName_2275_ = _args[3];
lean_object* v___x_2276_ = _args[4];
lean_object* v___x_2277_ = _args[5];
lean_object* v_a_2278_ = _args[6];
lean_object* v_val_2279_ = _args[7];
lean_object* v_inst_2280_ = _args[8];
lean_object* v_R_2281_ = _args[9];
lean_object* v_a_2282_ = _args[10];
lean_object* v_b_2283_ = _args[11];
lean_object* v_c_2284_ = _args[12];
lean_object* v___y_2285_ = _args[13];
lean_object* v___y_2286_ = _args[14];
lean_object* v___y_2287_ = _args[15];
lean_object* v___y_2288_ = _args[16];
lean_object* v___y_2289_ = _args[17];
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2272_, v___x_2273_, v___x_2274_, v_declName_2275_, v___x_2276_, v___x_2277_, v_a_2278_, v_val_2279_, v_inst_2280_, v_R_2281_, v_a_2282_, v_b_2283_, v_c_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec_ref(v_val_2279_);
lean_dec(v_a_2278_);
lean_dec(v___x_2276_);
lean_dec(v_declName_2275_);
lean_dec_ref(v___x_2274_);
lean_dec(v___x_2273_);
lean_dec(v_upperBound_2272_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v___x_2294_; 
v___x_2294_ = l_Lean_Expr_hasMVar(v_e_2291_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v_e_2291_);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v_mctx_2297_; lean_object* v___x_2298_; lean_object* v_fst_2299_; lean_object* v_snd_2300_; lean_object* v___x_2301_; lean_object* v_cache_2302_; lean_object* v_zetaDeltaFVarIds_2303_; lean_object* v_postponed_2304_; lean_object* v_diag_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
v___x_2296_ = lean_st_ref_get(v___y_2292_);
v_mctx_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_ref(v_mctx_2297_);
lean_dec(v___x_2296_);
v___x_2298_ = l_Lean_instantiateMVarsCore(v_mctx_2297_, v_e_2291_);
v_fst_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_fst_2299_);
v_snd_2300_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_snd_2300_);
lean_dec_ref(v___x_2298_);
v___x_2301_ = lean_st_ref_take(v___y_2292_);
v_cache_2302_ = lean_ctor_get(v___x_2301_, 1);
v_zetaDeltaFVarIds_2303_ = lean_ctor_get(v___x_2301_, 2);
v_postponed_2304_ = lean_ctor_get(v___x_2301_, 3);
v_diag_2305_ = lean_ctor_get(v___x_2301_, 4);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2315_);
v___x_2307_ = v___x_2301_;
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_diag_2305_);
lean_inc(v_postponed_2304_);
lean_inc(v_zetaDeltaFVarIds_2303_);
lean_inc(v_cache_2302_);
lean_dec(v___x_2301_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v_snd_2300_);
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_snd_2300_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_cache_2302_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_zetaDeltaFVarIds_2303_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_postponed_2304_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_diag_2305_);
v___x_2310_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_st_ref_set(v___y_2292_, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v_fst_2299_);
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2316_, v___y_2317_);
lean_dec(v___y_2317_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2320_, v___y_2322_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v_x_2344_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2351_, lean_object* v_e_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Meta_etaStruct_x3f(v_e_2352_, v_p_2351_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2378_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2378_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2378_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
if (lean_obj_tag(v_a_2359_) == 1)
{
lean_object* v_val_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2373_; 
v_val_2363_ = lean_ctor_get(v_a_2359_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_a_2359_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2365_ = v_a_2359_;
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_val_2363_);
lean_dec(v_a_2359_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 0);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_val_2363_);
v___x_2368_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2370_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2368_);
v___x_2370_ = v___x_2361_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
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
lean_object* v___x_2374_; lean_object* v___x_2376_; 
lean_dec(v_a_2359_);
v___x_2374_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2374_);
v___x_2376_ = v___x_2361_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
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
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2358_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2358_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2387_, lean_object* v_e_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2387_, v_e_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2395_, lean_object* v_x_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_apply_1(v_x_2396_, lean_box(0));
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2404_, v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2412_, lean_object* v_b_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
lean_dec(v_b_2413_);
lean_dec_ref(v_a_2412_);
return v_x_2414_;
}
else
{
lean_object* v_key_2415_; lean_object* v_value_2416_; lean_object* v_tail_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2429_; 
v_key_2415_ = lean_ctor_get(v_x_2414_, 0);
v_value_2416_ = lean_ctor_get(v_x_2414_, 1);
v_tail_2417_ = lean_ctor_get(v_x_2414_, 2);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_x_2414_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2419_ = v_x_2414_;
v_isShared_2420_ = v_isSharedCheck_2429_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_tail_2417_);
lean_inc(v_value_2416_);
lean_inc(v_key_2415_);
lean_dec(v_x_2414_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2429_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_ExprStructEq_beq(v_key_2415_, v_a_2412_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2412_, v_b_2413_, v_tail_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 2, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_key_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_value_2416_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
else
{
lean_object* v___x_2427_; 
lean_dec(v_value_2416_);
lean_dec(v_key_2415_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 1, v_b_2413_);
lean_ctor_set(v___x_2419_, 0, v_a_2412_);
v___x_2427_ = v___x_2419_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2412_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_b_2413_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_tail_2417_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
if (lean_obj_tag(v_x_2431_) == 0)
{
return v_x_2430_;
}
else
{
lean_object* v_key_2432_; lean_object* v_value_2433_; lean_object* v_tail_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2457_; 
v_key_2432_ = lean_ctor_get(v_x_2431_, 0);
v_value_2433_ = lean_ctor_get(v_x_2431_, 1);
v_tail_2434_ = lean_ctor_get(v_x_2431_, 2);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2431_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2436_ = v_x_2431_;
v_isShared_2437_ = v_isSharedCheck_2457_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_tail_2434_);
lean_inc(v_value_2433_);
lean_inc(v_key_2432_);
lean_dec(v_x_2431_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2457_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; uint64_t v_fold_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; uint64_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2438_ = lean_array_get_size(v_x_2430_);
v___x_2439_ = l_Lean_ExprStructEq_hash(v_key_2432_);
v___x_2440_ = 32ULL;
v___x_2441_ = lean_uint64_shift_right(v___x_2439_, v___x_2440_);
v_fold_2442_ = lean_uint64_xor(v___x_2439_, v___x_2441_);
v___x_2443_ = 16ULL;
v___x_2444_ = lean_uint64_shift_right(v_fold_2442_, v___x_2443_);
v___x_2445_ = lean_uint64_xor(v_fold_2442_, v___x_2444_);
v___x_2446_ = lean_uint64_to_usize(v___x_2445_);
v___x_2447_ = lean_usize_of_nat(v___x_2438_);
v___x_2448_ = ((size_t)1ULL);
v___x_2449_ = lean_usize_sub(v___x_2447_, v___x_2448_);
v___x_2450_ = lean_usize_land(v___x_2446_, v___x_2449_);
v___x_2451_ = lean_array_uget_borrowed(v_x_2430_, v___x_2450_);
lean_inc(v___x_2451_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 2, v___x_2451_);
v___x_2453_ = v___x_2436_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_key_2432_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_value_2433_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_array_uset(v_x_2430_, v___x_2450_, v___x_2453_);
v_x_2430_ = v___x_2454_;
v_x_2431_ = v_tail_2434_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2458_, lean_object* v_source_2459_, lean_object* v_target_2460_){
_start:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = lean_array_get_size(v_source_2459_);
v___x_2462_ = lean_nat_dec_lt(v_i_2458_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_dec_ref(v_source_2459_);
lean_dec(v_i_2458_);
return v_target_2460_;
}
else
{
lean_object* v_es_2463_; lean_object* v___x_2464_; lean_object* v_source_2465_; lean_object* v_target_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_es_2463_ = lean_array_fget(v_source_2459_, v_i_2458_);
v___x_2464_ = lean_box(0);
v_source_2465_ = lean_array_fset(v_source_2459_, v_i_2458_, v___x_2464_);
v_target_2466_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2460_, v_es_2463_);
v___x_2467_ = lean_unsigned_to_nat(1u);
v___x_2468_ = lean_nat_add(v_i_2458_, v___x_2467_);
lean_dec(v_i_2458_);
v_i_2458_ = v___x_2468_;
v_source_2459_ = v_source_2465_;
v_target_2460_ = v_target_2466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_nbuckets_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2471_ = lean_array_get_size(v_data_2470_);
v___x_2472_ = lean_unsigned_to_nat(2u);
v_nbuckets_2473_ = lean_nat_mul(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_mk_array(v_nbuckets_2473_, v___x_2475_);
v___x_2477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2474_, v_data_2470_, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2478_, lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
uint8_t v___x_2480_; 
v___x_2480_ = 0;
return v___x_2480_;
}
else
{
lean_object* v_key_2481_; lean_object* v_tail_2482_; uint8_t v___x_2483_; 
v_key_2481_ = lean_ctor_get(v_x_2479_, 0);
v_tail_2482_ = lean_ctor_get(v_x_2479_, 2);
v___x_2483_ = l_Lean_ExprStructEq_beq(v_key_2481_, v_a_2478_);
if (v___x_2483_ == 0)
{
v_x_2479_ = v_tail_2482_;
goto _start;
}
else
{
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v_res_2487_; lean_object* v_r_2488_; 
v_res_2487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2485_, v_x_2486_);
lean_dec(v_x_2486_);
lean_dec_ref(v_a_2485_);
v_r_2488_ = lean_box(v_res_2487_);
return v_r_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2489_, lean_object* v_a_2490_, lean_object* v_b_2491_){
_start:
{
lean_object* v_size_2492_; lean_object* v_buckets_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2536_; 
v_size_2492_ = lean_ctor_get(v_m_2489_, 0);
v_buckets_2493_ = lean_ctor_get(v_m_2489_, 1);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_m_2489_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2495_ = v_m_2489_;
v_isShared_2496_ = v_isSharedCheck_2536_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_buckets_2493_);
lean_inc(v_size_2492_);
lean_dec(v_m_2489_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2536_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v_fold_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; size_t v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; lean_object* v_bkt_2510_; uint8_t v___x_2511_; 
v___x_2497_ = lean_array_get_size(v_buckets_2493_);
v___x_2498_ = l_Lean_ExprStructEq_hash(v_a_2490_);
v___x_2499_ = 32ULL;
v___x_2500_ = lean_uint64_shift_right(v___x_2498_, v___x_2499_);
v_fold_2501_ = lean_uint64_xor(v___x_2498_, v___x_2500_);
v___x_2502_ = 16ULL;
v___x_2503_ = lean_uint64_shift_right(v_fold_2501_, v___x_2502_);
v___x_2504_ = lean_uint64_xor(v_fold_2501_, v___x_2503_);
v___x_2505_ = lean_uint64_to_usize(v___x_2504_);
v___x_2506_ = lean_usize_of_nat(v___x_2497_);
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_sub(v___x_2506_, v___x_2507_);
v___x_2509_ = lean_usize_land(v___x_2505_, v___x_2508_);
v_bkt_2510_ = lean_array_uget_borrowed(v_buckets_2493_, v___x_2509_);
v___x_2511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2490_, v_bkt_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; lean_object* v_size_x27_2513_; lean_object* v___x_2514_; lean_object* v_buckets_x27_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2512_ = lean_unsigned_to_nat(1u);
v_size_x27_2513_ = lean_nat_add(v_size_2492_, v___x_2512_);
lean_dec(v_size_2492_);
lean_inc(v_bkt_2510_);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2490_);
lean_ctor_set(v___x_2514_, 1, v_b_2491_);
lean_ctor_set(v___x_2514_, 2, v_bkt_2510_);
v_buckets_x27_2515_ = lean_array_uset(v_buckets_2493_, v___x_2509_, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(4u);
v___x_2517_ = lean_nat_mul(v_size_x27_2513_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(3u);
v___x_2519_ = lean_nat_div(v___x_2517_, v___x_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_array_get_size(v_buckets_x27_2515_);
v___x_2521_ = lean_nat_dec_le(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
if (v___x_2521_ == 0)
{
lean_object* v_val_2522_; lean_object* v___x_2524_; 
v_val_2522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2515_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v_val_2522_);
lean_ctor_set(v___x_2495_, 0, v_size_x27_2513_);
v___x_2524_ = v___x_2495_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_size_x27_2513_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_val_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
else
{
lean_object* v___x_2527_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v_buckets_x27_2515_);
lean_ctor_set(v___x_2495_, 0, v_size_x27_2513_);
v___x_2527_ = v___x_2495_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_size_x27_2513_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_buckets_x27_2515_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v_buckets_x27_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_inc(v_bkt_2510_);
v___x_2529_ = lean_box(0);
v_buckets_x27_2530_ = lean_array_uset(v_buckets_2493_, v___x_2509_, v___x_2529_);
v___x_2531_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2490_, v_b_2491_, v_bkt_2510_);
v___x_2532_ = lean_array_uset(v_buckets_x27_2530_, v___x_2509_, v___x_2531_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v___x_2532_);
v___x_2534_ = v___x_2495_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_size_2492_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2537_, lean_object* v_e_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_st_ref_take(v_a_2537_);
v___x_2542_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2541_, v_e_2538_, v_a_2539_);
v___x_2543_ = lean_st_ref_set(v_a_2537_, v___x_2542_);
v___x_2544_ = lean_box(0);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2545_, lean_object* v_e_2546_, lean_object* v_a_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2545_, v_e_2546_, v_a_2547_);
lean_dec(v_a_2545_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_apply_1(v_x_2551_, lean_box(0));
v___x_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2559_, v_x_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2567_, lean_object* v_x_2568_){
_start:
{
if (lean_obj_tag(v_x_2568_) == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_box(0);
return v___x_2569_;
}
else
{
lean_object* v_key_2570_; lean_object* v_value_2571_; lean_object* v_tail_2572_; uint8_t v___x_2573_; 
v_key_2570_ = lean_ctor_get(v_x_2568_, 0);
v_value_2571_ = lean_ctor_get(v_x_2568_, 1);
v_tail_2572_ = lean_ctor_get(v_x_2568_, 2);
v___x_2573_ = l_Lean_ExprStructEq_beq(v_key_2570_, v_a_2567_);
if (v___x_2573_ == 0)
{
v_x_2568_ = v_tail_2572_;
goto _start;
}
else
{
lean_object* v___x_2575_; 
lean_inc(v_value_2571_);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v_value_2571_);
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2576_, lean_object* v_x_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2576_, v_x_2577_);
lean_dec(v_x_2577_);
lean_dec_ref(v_a_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_buckets_2581_; lean_object* v___x_2582_; uint64_t v___x_2583_; uint64_t v___x_2584_; uint64_t v___x_2585_; uint64_t v_fold_2586_; uint64_t v___x_2587_; uint64_t v___x_2588_; uint64_t v___x_2589_; size_t v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_buckets_2581_ = lean_ctor_get(v_m_2579_, 1);
v___x_2582_ = lean_array_get_size(v_buckets_2581_);
v___x_2583_ = l_Lean_ExprStructEq_hash(v_a_2580_);
v___x_2584_ = 32ULL;
v___x_2585_ = lean_uint64_shift_right(v___x_2583_, v___x_2584_);
v_fold_2586_ = lean_uint64_xor(v___x_2583_, v___x_2585_);
v___x_2587_ = 16ULL;
v___x_2588_ = lean_uint64_shift_right(v_fold_2586_, v___x_2587_);
v___x_2589_ = lean_uint64_xor(v_fold_2586_, v___x_2588_);
v___x_2590_ = lean_uint64_to_usize(v___x_2589_);
v___x_2591_ = lean_usize_of_nat(v___x_2582_);
v___x_2592_ = ((size_t)1ULL);
v___x_2593_ = lean_usize_sub(v___x_2591_, v___x_2592_);
v___x_2594_ = lean_usize_land(v___x_2590_, v___x_2593_);
v___x_2595_ = lean_array_uget_borrowed(v_buckets_2581_, v___x_2594_);
v___x_2596_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2580_, v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2597_, v_a_2598_);
lean_dec_ref(v_a_2598_);
lean_dec_ref(v_m_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2600_, lean_object* v___y_2601_, lean_object* v_b_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2601_);
v___x_2608_ = lean_apply_7(v_k_2600_, v_b_2602_, v___y_2601_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2609_, lean_object* v___y_2610_, lean_object* v_b_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2609_, v___y_2610_, v_b_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2610_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2618_, uint8_t v_bi_2619_, lean_object* v_type_2620_, lean_object* v_k_2621_, uint8_t v_kind_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___f_2629_; lean_object* v___x_2630_; 
lean_inc(v___y_2623_);
v___f_2629_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2629_, 0, v_k_2621_);
lean_closure_set(v___f_2629_, 1, v___y_2623_);
v___x_2630_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2618_, v_bi_2619_, v_type_2620_, v___f_2629_, v_kind_2622_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2630_) == 0)
{
return v___x_2630_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2639_, lean_object* v_bi_2640_, lean_object* v_type_2641_, lean_object* v_k_2642_, lean_object* v_kind_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v_bi_boxed_2650_; uint8_t v_kind_boxed_2651_; lean_object* v_res_2652_; 
v_bi_boxed_2650_ = lean_unbox(v_bi_2640_);
v_kind_boxed_2651_ = lean_unbox(v_kind_2643_);
v_res_2652_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2639_, v_bi_boxed_2650_, v_type_2641_, v_k_2642_, v_kind_boxed_2651_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2653_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2667_, lean_object* v_type_2668_, lean_object* v_val_2669_, lean_object* v_k_2670_, uint8_t v_nondep_2671_, uint8_t v_kind_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___f_2679_; lean_object* v___x_2680_; 
lean_inc(v___y_2673_);
v___f_2679_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2679_, 0, v_k_2670_);
lean_closure_set(v___f_2679_, 1, v___y_2673_);
v___x_2680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2667_, v_type_2668_, v_val_2669_, v___f_2679_, v_nondep_2671_, v_kind_2672_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2680_) == 0)
{
return v___x_2680_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2689_, lean_object* v_type_2690_, lean_object* v_val_2691_, lean_object* v_k_2692_, lean_object* v_nondep_2693_, lean_object* v_kind_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v_nondep_boxed_2701_; uint8_t v_kind_boxed_2702_; lean_object* v_res_2703_; 
v_nondep_boxed_2701_ = lean_unbox(v_nondep_2693_);
v_kind_boxed_2702_ = lean_unbox(v_kind_2694_);
v_res_2703_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2689_, v_type_2690_, v_val_2691_, v_k_2692_, v_nondep_boxed_2701_, v_kind_boxed_2702_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
return v_res_2703_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = l_Lean_maxRecDepthErrorMessage;
v___x_2710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2712_ = l_Lean_MessageData_ofFormat(v___x_2711_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2714_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___x_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_ref_2716_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___y_2732_; lean_object* v_fileName_2741_; lean_object* v_fileMap_2742_; lean_object* v_options_2743_; lean_object* v_currRecDepth_2744_; lean_object* v_maxRecDepth_2745_; lean_object* v_ref_2746_; lean_object* v_currNamespace_2747_; lean_object* v_openDecls_2748_; lean_object* v_initHeartbeats_2749_; lean_object* v_maxHeartbeats_2750_; lean_object* v_quotContext_2751_; lean_object* v_currMacroScope_2752_; uint8_t v_diag_2753_; lean_object* v_cancelTk_x3f_2754_; uint8_t v_suppressElabErrors_2755_; lean_object* v_inheritedTraceOptions_2756_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_fileName_2741_ = lean_ctor_get(v___y_2728_, 0);
v_fileMap_2742_ = lean_ctor_get(v___y_2728_, 1);
v_options_2743_ = lean_ctor_get(v___y_2728_, 2);
v_currRecDepth_2744_ = lean_ctor_get(v___y_2728_, 3);
v_maxRecDepth_2745_ = lean_ctor_get(v___y_2728_, 4);
v_ref_2746_ = lean_ctor_get(v___y_2728_, 5);
v_currNamespace_2747_ = lean_ctor_get(v___y_2728_, 6);
v_openDecls_2748_ = lean_ctor_get(v___y_2728_, 7);
v_initHeartbeats_2749_ = lean_ctor_get(v___y_2728_, 8);
v_maxHeartbeats_2750_ = lean_ctor_get(v___y_2728_, 9);
v_quotContext_2751_ = lean_ctor_get(v___y_2728_, 10);
v_currMacroScope_2752_ = lean_ctor_get(v___y_2728_, 11);
v_diag_2753_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*14);
v_cancelTk_x3f_2754_ = lean_ctor_get(v___y_2728_, 12);
v_suppressElabErrors_2755_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2756_ = lean_ctor_get(v___y_2728_, 13);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_nat_dec_eq(v_maxRecDepth_2745_, v___x_2762_);
if (v___x_2763_ == 0)
{
uint8_t v___x_2764_; 
v___x_2764_ = lean_nat_dec_eq(v_currRecDepth_2744_, v_maxRecDepth_2745_);
if (v___x_2764_ == 0)
{
goto v___jp_2757_;
}
else
{
lean_object* v___x_2765_; 
lean_dec_ref(v_x_2724_);
lean_inc(v_ref_2746_);
v___x_2765_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2746_);
v___y_2732_ = v___x_2765_;
goto v___jp_2731_;
}
}
else
{
goto v___jp_2757_;
}
v___jp_2731_:
{
if (lean_obj_tag(v___y_2732_) == 0)
{
return v___y_2732_;
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2733_ = lean_ctor_get(v___y_2732_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___y_2732_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___y_2732_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___y_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
v___jp_2757_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_unsigned_to_nat(1u);
v___x_2759_ = lean_nat_add(v_currRecDepth_2744_, v___x_2758_);
lean_inc_ref(v_inheritedTraceOptions_2756_);
lean_inc(v_cancelTk_x3f_2754_);
lean_inc(v_currMacroScope_2752_);
lean_inc(v_quotContext_2751_);
lean_inc(v_maxHeartbeats_2750_);
lean_inc(v_initHeartbeats_2749_);
lean_inc(v_openDecls_2748_);
lean_inc(v_currNamespace_2747_);
lean_inc(v_ref_2746_);
lean_inc(v_maxRecDepth_2745_);
lean_inc_ref(v_options_2743_);
lean_inc_ref(v_fileMap_2742_);
lean_inc_ref(v_fileName_2741_);
v___x_2760_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2760_, 0, v_fileName_2741_);
lean_ctor_set(v___x_2760_, 1, v_fileMap_2742_);
lean_ctor_set(v___x_2760_, 2, v_options_2743_);
lean_ctor_set(v___x_2760_, 3, v___x_2759_);
lean_ctor_set(v___x_2760_, 4, v_maxRecDepth_2745_);
lean_ctor_set(v___x_2760_, 5, v_ref_2746_);
lean_ctor_set(v___x_2760_, 6, v_currNamespace_2747_);
lean_ctor_set(v___x_2760_, 7, v_openDecls_2748_);
lean_ctor_set(v___x_2760_, 8, v_initHeartbeats_2749_);
lean_ctor_set(v___x_2760_, 9, v_maxHeartbeats_2750_);
lean_ctor_set(v___x_2760_, 10, v_quotContext_2751_);
lean_ctor_set(v___x_2760_, 11, v_currMacroScope_2752_);
lean_ctor_set(v___x_2760_, 12, v_cancelTk_x3f_2754_);
lean_ctor_set(v___x_2760_, 13, v_inheritedTraceOptions_2756_);
lean_ctor_set_uint8(v___x_2760_, sizeof(void*)*14, v_diag_2753_);
lean_ctor_set_uint8(v___x_2760_, sizeof(void*)*14 + 1, v_suppressElabErrors_2755_);
lean_inc(v___y_2729_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
v___x_2761_ = lean_apply_6(v_x_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___x_2760_, v___y_2729_, lean_box(0));
v___y_2732_ = v___x_2761_;
goto v___jp_2731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2777_, lean_object* v_pre_2778_, lean_object* v_post_2779_, uint8_t v_usedLetOnly_2780_, uint8_t v_skipConstInApp_2781_, uint8_t v_skipInstances_2782_, lean_object* v_body_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_array_push(v_fvars_2777_, v_x_2784_);
v___x_2792_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2778_, v_post_2779_, v_usedLetOnly_2780_, v_skipConstInApp_2781_, v_skipInstances_2782_, v___x_2791_, v_body_2783_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2793_, lean_object* v_pre_2794_, lean_object* v_post_2795_, lean_object* v_usedLetOnly_2796_, lean_object* v_skipConstInApp_2797_, lean_object* v_skipInstances_2798_, lean_object* v_body_2799_, lean_object* v_x_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v_usedLetOnly_boxed_2807_; uint8_t v_skipConstInApp_boxed_2808_; uint8_t v_skipInstances_boxed_2809_; lean_object* v_res_2810_; 
v_usedLetOnly_boxed_2807_ = lean_unbox(v_usedLetOnly_2796_);
v_skipConstInApp_boxed_2808_ = lean_unbox(v_skipConstInApp_2797_);
v_skipInstances_boxed_2809_ = lean_unbox(v_skipInstances_2798_);
v_res_2810_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2793_, v_pre_2794_, v_post_2795_, v_usedLetOnly_boxed_2807_, v_skipConstInApp_boxed_2808_, v_skipInstances_boxed_2809_, v_body_2799_, v_x_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2811_, lean_object* v_post_2812_, uint8_t v_usedLetOnly_2813_, uint8_t v_skipConstInApp_2814_, uint8_t v_skipInstances_2815_, lean_object* v_e_2816_, lean_object* v_a_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
lean_inc_ref(v_post_2812_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc_ref(v_e_2816_);
v___x_2823_ = lean_apply_6(v_post_2812_, v_e_2816_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2842_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2842_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2842_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
switch(lean_obj_tag(v_a_2824_))
{
case 0:
{
lean_object* v_e_2828_; lean_object* v___x_2830_; 
lean_dec_ref(v_e_2816_);
lean_dec_ref(v_post_2812_);
lean_dec_ref(v_pre_2811_);
v_e_2828_ = lean_ctor_get(v_a_2824_, 0);
lean_inc_ref(v_e_2828_);
lean_dec_ref(v_a_2824_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_e_2828_);
v___x_2830_ = v___x_2826_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_e_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
case 1:
{
lean_object* v_e_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2826_);
lean_dec_ref(v_e_2816_);
v_e_2832_ = lean_ctor_get(v_a_2824_, 0);
lean_inc_ref(v_e_2832_);
lean_dec_ref(v_a_2824_);
v___x_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2811_, v_post_2812_, v_usedLetOnly_2813_, v_skipConstInApp_2814_, v_skipInstances_2815_, v_e_2832_, v_a_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2833_;
}
default: 
{
lean_object* v_e_x3f_2834_; 
lean_dec_ref(v_post_2812_);
lean_dec_ref(v_pre_2811_);
v_e_x3f_2834_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_e_x3f_2834_);
lean_dec_ref(v_a_2824_);
if (lean_obj_tag(v_e_x3f_2834_) == 0)
{
lean_object* v___x_2836_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_e_2816_);
v___x_2836_ = v___x_2826_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_e_2816_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
lean_object* v_val_2838_; lean_object* v___x_2840_; 
lean_dec_ref(v_e_2816_);
v_val_2838_ = lean_ctor_get(v_e_x3f_2834_, 0);
lean_inc(v_val_2838_);
lean_dec_ref(v_e_x3f_2834_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v_val_2838_);
v___x_2840_ = v___x_2826_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_val_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_e_2816_);
lean_dec_ref(v_post_2812_);
lean_dec_ref(v_pre_2811_);
v_a_2843_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2823_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2823_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2851_, lean_object* v_post_2852_, uint8_t v_usedLetOnly_2853_, uint8_t v_skipConstInApp_2854_, uint8_t v_skipInstances_2855_, lean_object* v_fvars_2856_, lean_object* v_e_2857_, lean_object* v_a_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
if (lean_obj_tag(v_e_2857_) == 6)
{
lean_object* v_binderName_2864_; lean_object* v_binderType_2865_; lean_object* v_body_2866_; uint8_t v_binderInfo_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_binderName_2864_ = lean_ctor_get(v_e_2857_, 0);
lean_inc(v_binderName_2864_);
v_binderType_2865_ = lean_ctor_get(v_e_2857_, 1);
lean_inc_ref(v_binderType_2865_);
v_body_2866_ = lean_ctor_get(v_e_2857_, 2);
lean_inc_ref(v_body_2866_);
v_binderInfo_2867_ = lean_ctor_get_uint8(v_e_2857_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2857_);
v___x_2868_ = lean_expr_instantiate_rev(v_binderType_2865_, v_fvars_2856_);
lean_dec_ref(v_binderType_2865_);
lean_inc_ref(v_post_2852_);
lean_inc_ref(v_pre_2851_);
v___x_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v___x_2868_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___f_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_box(v_usedLetOnly_2853_);
v___x_2872_ = lean_box(v_skipConstInApp_2854_);
v___x_2873_ = lean_box(v_skipInstances_2855_);
v___f_2874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2874_, 0, v_fvars_2856_);
lean_closure_set(v___f_2874_, 1, v_pre_2851_);
lean_closure_set(v___f_2874_, 2, v_post_2852_);
lean_closure_set(v___f_2874_, 3, v___x_2871_);
lean_closure_set(v___f_2874_, 4, v___x_2872_);
lean_closure_set(v___f_2874_, 5, v___x_2873_);
lean_closure_set(v___f_2874_, 6, v_body_2866_);
v___x_2875_ = 0;
v___x_2876_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2864_, v_binderInfo_2867_, v_a_2870_, v___f_2874_, v___x_2875_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
return v___x_2876_;
}
else
{
lean_dec_ref(v_body_2866_);
lean_dec(v_binderName_2864_);
lean_dec_ref(v_fvars_2856_);
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
return v___x_2869_;
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_expr_instantiate_rev(v_e_2857_, v_fvars_2856_);
lean_dec_ref(v_e_2857_);
lean_inc_ref(v_post_2852_);
lean_inc_ref(v_pre_2851_);
v___x_2878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v___x_2877_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; uint8_t v___x_2880_; uint8_t v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = 0;
v___x_2881_ = 1;
v___x_2882_ = 1;
v___x_2883_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2856_, v_a_2879_, v___x_2880_, v_usedLetOnly_2853_, v___x_2880_, v___x_2881_, v___x_2882_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec_ref(v_fvars_2856_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v_a_2884_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
return v___x_2885_;
}
else
{
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
return v___x_2883_;
}
}
else
{
lean_dec_ref(v_fvars_2856_);
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
return v___x_2878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2886_, lean_object* v_pre_2887_, lean_object* v_post_2888_, uint8_t v_usedLetOnly_2889_, uint8_t v_skipConstInApp_2890_, uint8_t v_skipInstances_2891_, lean_object* v_body_2892_, lean_object* v_x_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_array_push(v_fvars_2886_, v_x_2893_);
v___x_2901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2887_, v_post_2888_, v_usedLetOnly_2889_, v_skipConstInApp_2890_, v_skipInstances_2891_, v___x_2900_, v_body_2892_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2902_, lean_object* v_pre_2903_, lean_object* v_post_2904_, lean_object* v_usedLetOnly_2905_, lean_object* v_skipConstInApp_2906_, lean_object* v_skipInstances_2907_, lean_object* v_body_2908_, lean_object* v_x_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
uint8_t v_usedLetOnly_boxed_2916_; uint8_t v_skipConstInApp_boxed_2917_; uint8_t v_skipInstances_boxed_2918_; lean_object* v_res_2919_; 
v_usedLetOnly_boxed_2916_ = lean_unbox(v_usedLetOnly_2905_);
v_skipConstInApp_boxed_2917_ = lean_unbox(v_skipConstInApp_2906_);
v_skipInstances_boxed_2918_ = lean_unbox(v_skipInstances_2907_);
v_res_2919_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2902_, v_pre_2903_, v_post_2904_, v_usedLetOnly_boxed_2916_, v_skipConstInApp_boxed_2917_, v_skipInstances_boxed_2918_, v_body_2908_, v_x_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2920_, lean_object* v_post_2921_, uint8_t v_usedLetOnly_2922_, uint8_t v_skipConstInApp_2923_, uint8_t v_skipInstances_2924_, lean_object* v_fvars_2925_, lean_object* v_e_2926_, lean_object* v_a_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
if (lean_obj_tag(v_e_2926_) == 8)
{
lean_object* v_declName_2933_; lean_object* v_type_2934_; lean_object* v_value_2935_; lean_object* v_body_2936_; uint8_t v_nondep_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_declName_2933_ = lean_ctor_get(v_e_2926_, 0);
lean_inc(v_declName_2933_);
v_type_2934_ = lean_ctor_get(v_e_2926_, 1);
lean_inc_ref(v_type_2934_);
v_value_2935_ = lean_ctor_get(v_e_2926_, 2);
lean_inc_ref(v_value_2935_);
v_body_2936_ = lean_ctor_get(v_e_2926_, 3);
lean_inc_ref(v_body_2936_);
v_nondep_2937_ = lean_ctor_get_uint8(v_e_2926_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2926_);
v___x_2938_ = lean_expr_instantiate_rev(v_type_2934_, v_fvars_2925_);
lean_dec_ref(v_type_2934_);
lean_inc_ref(v_post_2921_);
lean_inc_ref(v_pre_2920_);
v___x_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v___x_2938_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = lean_expr_instantiate_rev(v_value_2935_, v_fvars_2925_);
lean_dec_ref(v_value_2935_);
lean_inc_ref(v_post_2921_);
lean_inc_ref(v_pre_2920_);
v___x_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v___x_2941_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = lean_box(v_usedLetOnly_2922_);
v___x_2945_ = lean_box(v_skipConstInApp_2923_);
v___x_2946_ = lean_box(v_skipInstances_2924_);
v___f_2947_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2947_, 0, v_fvars_2925_);
lean_closure_set(v___f_2947_, 1, v_pre_2920_);
lean_closure_set(v___f_2947_, 2, v_post_2921_);
lean_closure_set(v___f_2947_, 3, v___x_2944_);
lean_closure_set(v___f_2947_, 4, v___x_2945_);
lean_closure_set(v___f_2947_, 5, v___x_2946_);
lean_closure_set(v___f_2947_, 6, v_body_2936_);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2933_, v_a_2940_, v_a_2943_, v___f_2947_, v_nondep_2937_, v___x_2948_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2949_;
}
else
{
lean_dec(v_a_2940_);
lean_dec_ref(v_body_2936_);
lean_dec(v_declName_2933_);
lean_dec_ref(v_fvars_2925_);
lean_dec_ref(v_post_2921_);
lean_dec_ref(v_pre_2920_);
return v___x_2942_;
}
}
else
{
lean_dec_ref(v_body_2936_);
lean_dec_ref(v_value_2935_);
lean_dec(v_declName_2933_);
lean_dec_ref(v_fvars_2925_);
lean_dec_ref(v_post_2921_);
lean_dec_ref(v_pre_2920_);
return v___x_2939_;
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_expr_instantiate_rev(v_e_2926_, v_fvars_2925_);
lean_dec_ref(v_e_2926_);
lean_inc_ref(v_post_2921_);
lean_inc_ref(v_pre_2920_);
v___x_2951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v___x_2950_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; uint8_t v___x_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = 0;
v___x_2954_ = 1;
v___x_2955_ = l_Lean_Meta_mkLetFVars(v_fvars_2925_, v_a_2952_, v_usedLetOnly_2922_, v___x_2953_, v___x_2954_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec_ref(v_fvars_2925_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2955_);
v___x_2957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v_a_2956_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2957_;
}
else
{
lean_dec_ref(v_post_2921_);
lean_dec_ref(v_pre_2920_);
return v___x_2955_;
}
}
else
{
lean_dec_ref(v_fvars_2925_);
lean_dec_ref(v_post_2921_);
lean_dec_ref(v_pre_2920_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2958_, lean_object* v_post_2959_, uint8_t v_usedLetOnly_2960_, uint8_t v_skipConstInApp_2961_, uint8_t v_skipInstances_2962_, size_t v_sz_2963_, size_t v_i_2964_, lean_object* v_bs_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_usize_dec_lt(v_i_2964_, v_sz_2963_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec_ref(v_post_2959_);
lean_dec_ref(v_pre_2958_);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_bs_2965_);
return v___x_2973_;
}
else
{
lean_object* v_v_2974_; lean_object* v___x_2975_; 
v_v_2974_ = lean_array_uget_borrowed(v_bs_2965_, v_i_2964_);
lean_inc(v_v_2974_);
lean_inc_ref(v_post_2959_);
lean_inc_ref(v_pre_2958_);
v___x_2975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2958_, v_post_2959_, v_usedLetOnly_2960_, v_skipConstInApp_2961_, v_skipInstances_2962_, v_v_2974_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v_bs_x27_2978_; size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v_bs_x27_2978_ = lean_array_uset(v_bs_2965_, v_i_2964_, v___x_2977_);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_add(v_i_2964_, v___x_2979_);
v___x_2981_ = lean_array_uset(v_bs_x27_2978_, v_i_2964_, v_a_2976_);
v_i_2964_ = v___x_2980_;
v_bs_2965_ = v___x_2981_;
goto _start;
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_bs_2965_);
lean_dec_ref(v_post_2959_);
lean_dec_ref(v_pre_2958_);
v_a_2983_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2975_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2975_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2991_, lean_object* v_post_2992_, uint8_t v_usedLetOnly_2993_, uint8_t v_skipConstInApp_2994_, uint8_t v_skipInstances_2995_, lean_object* v___x_2996_, lean_object* v___y_2997_, lean_object* v_b_2998_, lean_object* v_a_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2991_, v_post_2992_, v_usedLetOnly_2993_, v_skipConstInApp_2994_, v_skipInstances_2995_, v___x_2996_, v___y_2997_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3015_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3015_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3010_ = lean_array_fset(v_b_2998_, v_a_2999_, v_a_3006_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3011_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_b_2998_);
v_a_3016_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3005_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3005_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3024_, lean_object* v_post_3025_, lean_object* v_usedLetOnly_3026_, lean_object* v_skipConstInApp_3027_, lean_object* v_skipInstances_3028_, lean_object* v___x_3029_, lean_object* v___y_3030_, lean_object* v_b_3031_, lean_object* v_a_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v_usedLetOnly_boxed_3038_; uint8_t v_skipConstInApp_boxed_3039_; uint8_t v_skipInstances_boxed_3040_; lean_object* v_res_3041_; 
v_usedLetOnly_boxed_3038_ = lean_unbox(v_usedLetOnly_3026_);
v_skipConstInApp_boxed_3039_ = lean_unbox(v_skipConstInApp_3027_);
v_skipInstances_boxed_3040_ = lean_unbox(v_skipInstances_3028_);
v_res_3041_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3024_, v_post_3025_, v_usedLetOnly_boxed_3038_, v_skipConstInApp_boxed_3039_, v_skipInstances_boxed_3040_, v___x_3029_, v___y_3030_, v_b_3031_, v_a_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v_a_3032_);
lean_dec(v___y_3030_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3042_, lean_object* v___x_3043_, lean_object* v_pre_3044_, lean_object* v_post_3045_, uint8_t v_usedLetOnly_3046_, uint8_t v_skipConstInApp_3047_, uint8_t v_skipInstances_3048_, lean_object* v_a_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___y_3058_; uint8_t v___x_3081_; 
v___x_3081_ = lean_nat_dec_lt(v_a_3049_, v_upperBound_3042_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v_a_3049_);
lean_dec_ref(v_post_3045_);
lean_dec_ref(v_pre_3044_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_b_3050_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3083_ = lean_array_fget_borrowed(v_b_3050_, v_a_3049_);
v___x_3084_ = lean_array_get_size(v___x_3043_);
v___x_3085_ = lean_nat_dec_lt(v_a_3049_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; 
lean_inc(v___x_3083_);
v___x_3086_ = lean_box(v_usedLetOnly_3046_);
v___x_3087_ = lean_box(v_skipConstInApp_3047_);
v___x_3088_ = lean_box(v_skipInstances_3048_);
lean_inc(v_a_3049_);
lean_inc(v___y_3051_);
lean_inc_ref(v_post_3045_);
lean_inc_ref(v_pre_3044_);
v___f_3089_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3089_, 0, v_pre_3044_);
lean_closure_set(v___f_3089_, 1, v_post_3045_);
lean_closure_set(v___f_3089_, 2, v___x_3086_);
lean_closure_set(v___f_3089_, 3, v___x_3087_);
lean_closure_set(v___f_3089_, 4, v___x_3088_);
lean_closure_set(v___f_3089_, 5, v___x_3083_);
lean_closure_set(v___f_3089_, 6, v___y_3051_);
lean_closure_set(v___f_3089_, 7, v_b_3050_);
lean_closure_set(v___f_3089_, 8, v_a_3049_);
v___y_3058_ = v___f_3089_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3090_; uint8_t v_isInstance_3091_; 
v___x_3090_ = lean_array_fget_borrowed(v___x_3043_, v_a_3049_);
v_isInstance_3091_ = lean_ctor_get_uint8(v___x_3090_, sizeof(void*)*1 + 4);
if (v_isInstance_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___f_3095_; 
lean_inc(v___x_3083_);
v___x_3092_ = lean_box(v_usedLetOnly_3046_);
v___x_3093_ = lean_box(v_skipConstInApp_3047_);
v___x_3094_ = lean_box(v_skipInstances_3048_);
lean_inc(v_a_3049_);
lean_inc(v___y_3051_);
lean_inc_ref(v_post_3045_);
lean_inc_ref(v_pre_3044_);
v___f_3095_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3095_, 0, v_pre_3044_);
lean_closure_set(v___f_3095_, 1, v_post_3045_);
lean_closure_set(v___f_3095_, 2, v___x_3092_);
lean_closure_set(v___f_3095_, 3, v___x_3093_);
lean_closure_set(v___f_3095_, 4, v___x_3094_);
lean_closure_set(v___f_3095_, 5, v___x_3083_);
lean_closure_set(v___f_3095_, 6, v___y_3051_);
lean_closure_set(v___f_3095_, 7, v_b_3050_);
lean_closure_set(v___f_3095_, 8, v_a_3049_);
v___y_3058_ = v___f_3095_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3096_; lean_object* v___f_3097_; 
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_b_3050_);
v___f_3097_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3097_, 0, v___x_3096_);
v___y_3058_ = v___f_3097_;
goto v___jp_3057_;
}
}
}
v___jp_3057_:
{
lean_object* v___x_3059_; 
lean_inc(v___y_3055_);
lean_inc_ref(v___y_3054_);
lean_inc(v___y_3053_);
lean_inc_ref(v___y_3052_);
v___x_3059_ = lean_apply_5(v___y_3058_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, lean_box(0));
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3072_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3072_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3072_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
if (lean_obj_tag(v_a_3060_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; 
lean_dec(v_a_3049_);
lean_dec_ref(v_post_3045_);
lean_dec_ref(v_pre_3044_);
v_a_3064_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v_a_3060_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v_a_3064_);
v___x_3066_ = v___x_3062_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_del_object(v___x_3062_);
v_a_3068_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v_a_3060_);
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_add(v_a_3049_, v___x_3069_);
lean_dec(v_a_3049_);
v_a_3049_ = v___x_3070_;
v_b_3050_ = v_a_3068_;
goto _start;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_3049_);
lean_dec_ref(v_post_3045_);
lean_dec_ref(v_pre_3044_);
v_a_3073_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3059_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3059_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3098_, lean_object* v_pre_3099_, lean_object* v_post_3100_, uint8_t v_usedLetOnly_3101_, uint8_t v_skipConstInApp_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_f_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; 
if (lean_obj_tag(v_x_3103_) == 5)
{
lean_object* v_fn_3161_; lean_object* v_arg_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_fn_3161_ = lean_ctor_get(v_x_3103_, 0);
lean_inc_ref(v_fn_3161_);
v_arg_3162_ = lean_ctor_get(v_x_3103_, 1);
lean_inc_ref(v_arg_3162_);
lean_dec_ref(v_x_3103_);
v___x_3163_ = lean_array_set(v_x_3104_, v_x_3105_, v_arg_3162_);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_nat_sub(v_x_3105_, v___x_3164_);
lean_dec(v_x_3105_);
v_x_3103_ = v_fn_3161_;
v_x_3104_ = v___x_3163_;
v_x_3105_ = v___x_3165_;
goto _start;
}
else
{
lean_dec(v_x_3105_);
if (v_skipConstInApp_3102_ == 0)
{
goto v___jp_3158_;
}
else
{
uint8_t v___x_3167_; 
v___x_3167_ = l_Lean_Expr_isConst(v_x_3103_);
if (v___x_3167_ == 0)
{
goto v___jp_3158_;
}
else
{
v_f_3113_ = v_x_3103_;
v___y_3114_ = v___y_3106_;
v___y_3115_ = v___y_3107_;
v___y_3116_ = v___y_3108_;
v___y_3117_ = v___y_3109_;
v___y_3118_ = v___y_3110_;
goto v___jp_3112_;
}
}
}
v___jp_3112_:
{
if (v_skipInstances_3098_ == 0)
{
size_t v_sz_3119_; size_t v___x_3120_; lean_object* v___x_3121_; 
v_sz_3119_ = lean_array_size(v_x_3104_);
v___x_3120_ = ((size_t)0ULL);
lean_inc_ref(v_post_3100_);
lean_inc_ref(v_pre_3099_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3098_, v_sz_3119_, v___x_3120_, v_x_3104_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref(v___x_3121_);
v___x_3123_ = l_Lean_mkAppN(v_f_3113_, v_a_3122_);
lean_dec(v_a_3122_);
v___x_3124_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3098_, v___x_3123_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3124_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v_f_3113_);
lean_dec_ref(v_post_3100_);
lean_dec_ref(v_pre_3099_);
v_a_3125_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3121_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3121_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_array_get_size(v_x_3104_);
lean_inc_ref(v_f_3113_);
v___x_3134_ = l_Lean_Meta_getFunInfoNArgs(v_f_3113_, v___x_3133_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v_paramInfo_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3134_);
v_paramInfo_3136_ = lean_ctor_get(v_a_3135_, 0);
lean_inc_ref(v_paramInfo_3136_);
lean_dec(v_a_3135_);
v___x_3137_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3100_);
lean_inc_ref(v_pre_3099_);
v___x_3138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3133_, v_paramInfo_3136_, v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3098_, v___x_3137_, v_x_3104_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec_ref(v_paramInfo_3136_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = l_Lean_mkAppN(v_f_3113_, v_a_3139_);
lean_dec(v_a_3139_);
v___x_3141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3098_, v___x_3140_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3141_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v_f_3113_);
lean_dec_ref(v_post_3100_);
lean_dec_ref(v_pre_3099_);
v_a_3142_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3138_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3138_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_f_3113_);
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_post_3100_);
lean_dec_ref(v_pre_3099_);
v_a_3150_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3134_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3134_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
v___jp_3158_:
{
lean_object* v___x_3159_; 
lean_inc_ref(v_post_3100_);
lean_inc_ref(v_pre_3099_);
v___x_3159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3099_, v_post_3100_, v_usedLetOnly_3101_, v_skipConstInApp_3102_, v_skipInstances_3098_, v_x_3103_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v_f_3113_ = v_a_3160_;
v___y_3114_ = v___y_3106_;
v___y_3115_ = v___y_3107_;
v___y_3116_ = v___y_3108_;
v___y_3117_ = v___y_3109_;
v___y_3118_ = v___y_3110_;
goto v___jp_3112_;
}
else
{
lean_dec_ref(v_x_3104_);
lean_dec_ref(v_post_3100_);
lean_dec_ref(v_pre_3099_);
return v___x_3159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3168_, lean_object* v_pre_3169_, lean_object* v_e_3170_, lean_object* v_post_3171_, uint8_t v_usedLetOnly_3172_, uint8_t v_skipConstInApp_3173_, uint8_t v_skipInstances_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Core_checkSystem(v___x_3168_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v___x_3182_; 
lean_dec_ref(v___x_3181_);
lean_inc_ref(v_pre_3169_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc_ref(v_e_3170_);
v___x_3182_ = lean_apply_6(v_pre_3169_, v_e_3170_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, lean_box(0));
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3231_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3231_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3231_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___y_3188_; 
switch(lean_obj_tag(v_a_3183_))
{
case 0:
{
lean_object* v_e_3223_; lean_object* v___x_3225_; 
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_e_3170_);
lean_dec_ref(v_pre_3169_);
v_e_3223_ = lean_ctor_get(v_a_3183_, 0);
lean_inc_ref(v_e_3223_);
lean_dec_ref(v_a_3183_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v_e_3223_);
v___x_3225_ = v___x_3185_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_e_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
case 1:
{
lean_object* v_e_3227_; lean_object* v___x_3228_; 
lean_del_object(v___x_3185_);
lean_dec_ref(v_e_3170_);
v_e_3227_ = lean_ctor_get(v_a_3183_, 0);
lean_inc_ref(v_e_3227_);
lean_dec_ref(v_a_3183_);
v___x_3228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v_e_3227_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3228_;
}
default: 
{
lean_object* v_e_x3f_3229_; 
lean_del_object(v___x_3185_);
v_e_x3f_3229_ = lean_ctor_get(v_a_3183_, 0);
lean_inc(v_e_x3f_3229_);
lean_dec_ref(v_a_3183_);
if (lean_obj_tag(v_e_x3f_3229_) == 0)
{
v___y_3188_ = v_e_3170_;
goto v___jp_3187_;
}
else
{
lean_object* v_val_3230_; 
lean_dec_ref(v_e_3170_);
v_val_3230_ = lean_ctor_get(v_e_x3f_3229_, 0);
lean_inc(v_val_3230_);
lean_dec_ref(v_e_x3f_3229_);
v___y_3188_ = v_val_3230_;
goto v___jp_3187_;
}
}
}
v___jp_3187_:
{
switch(lean_obj_tag(v___y_3188_))
{
case 7:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___x_3189_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3190_;
}
case 6:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___x_3191_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3192_;
}
case 8:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3194_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___x_3193_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3194_;
}
case 5:
{
lean_object* v_dummy_3195_; lean_object* v_nargs_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_dummy_3195_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3196_ = l_Lean_Expr_getAppNumArgs(v___y_3188_);
lean_inc(v_nargs_3196_);
v___x_3197_ = lean_mk_array(v_nargs_3196_, v_dummy_3195_);
v___x_3198_ = lean_unsigned_to_nat(1u);
v___x_3199_ = lean_nat_sub(v_nargs_3196_, v___x_3198_);
lean_dec(v_nargs_3196_);
v___x_3200_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3174_, v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v___y_3188_, v___x_3197_, v___x_3199_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3200_;
}
case 10:
{
lean_object* v_data_3201_; lean_object* v_expr_3202_; lean_object* v___x_3203_; 
v_data_3201_ = lean_ctor_get(v___y_3188_, 0);
v_expr_3202_ = lean_ctor_get(v___y_3188_, 1);
lean_inc_ref(v_expr_3202_);
lean_inc_ref(v_post_3171_);
lean_inc_ref(v_pre_3169_);
v___x_3203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v_expr_3202_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; size_t v___x_3205_; size_t v___x_3206_; uint8_t v___x_3207_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = lean_ptr_addr(v_expr_3202_);
v___x_3206_ = lean_ptr_addr(v_a_3204_);
v___x_3207_ = lean_usize_dec_eq(v___x_3205_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_inc(v_data_3201_);
lean_dec_ref(v___y_3188_);
v___x_3208_ = l_Lean_Expr_mdata___override(v_data_3201_, v_a_3204_);
v___x_3209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___x_3208_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3209_;
}
else
{
lean_object* v___x_3210_; 
lean_dec(v_a_3204_);
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3210_;
}
}
else
{
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_pre_3169_);
return v___x_3203_;
}
}
case 11:
{
lean_object* v_typeName_3211_; lean_object* v_idx_3212_; lean_object* v_struct_3213_; lean_object* v___x_3214_; 
v_typeName_3211_ = lean_ctor_get(v___y_3188_, 0);
v_idx_3212_ = lean_ctor_get(v___y_3188_, 1);
v_struct_3213_ = lean_ctor_get(v___y_3188_, 2);
lean_inc_ref(v_struct_3213_);
lean_inc_ref(v_post_3171_);
lean_inc_ref(v_pre_3169_);
v___x_3214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v_struct_3213_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; size_t v___x_3216_; size_t v___x_3217_; uint8_t v___x_3218_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
v___x_3216_ = lean_ptr_addr(v_struct_3213_);
v___x_3217_ = lean_ptr_addr(v_a_3215_);
v___x_3218_ = lean_usize_dec_eq(v___x_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_inc(v_idx_3212_);
lean_inc(v_typeName_3211_);
lean_dec_ref(v___y_3188_);
v___x_3219_ = l_Lean_Expr_proj___override(v_typeName_3211_, v_idx_3212_, v_a_3215_);
v___x_3220_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___x_3219_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; 
lean_dec(v_a_3215_);
v___x_3221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3221_;
}
}
else
{
lean_dec_ref(v___y_3188_);
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_pre_3169_);
return v___x_3214_;
}
}
default: 
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v___y_3188_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3222_;
}
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_e_3170_);
lean_dec_ref(v_pre_3169_);
v_a_3232_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3182_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3182_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v_post_3171_);
lean_dec_ref(v_e_3170_);
lean_dec_ref(v_pre_3169_);
v_a_3240_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3181_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3181_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3248_, lean_object* v_pre_3249_, lean_object* v_e_3250_, lean_object* v_post_3251_, lean_object* v_usedLetOnly_3252_, lean_object* v_skipConstInApp_3253_, lean_object* v_skipInstances_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_usedLetOnly_boxed_3261_; uint8_t v_skipConstInApp_boxed_3262_; uint8_t v_skipInstances_boxed_3263_; lean_object* v_res_3264_; 
v_usedLetOnly_boxed_3261_ = lean_unbox(v_usedLetOnly_3252_);
v_skipConstInApp_boxed_3262_ = lean_unbox(v_skipConstInApp_3253_);
v_skipInstances_boxed_3263_ = lean_unbox(v_skipInstances_3254_);
v_res_3264_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3248_, v_pre_3249_, v_e_3250_, v_post_3251_, v_usedLetOnly_boxed_3261_, v_skipConstInApp_boxed_3262_, v_skipInstances_boxed_3263_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3265_, lean_object* v_post_3266_, uint8_t v_usedLetOnly_3267_, uint8_t v_skipConstInApp_3268_, uint8_t v_skipInstances_3269_, lean_object* v_e_3270_, lean_object* v_a_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_inc(v_a_3271_);
v___x_3277_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3277_, 0, lean_box(0));
lean_closure_set(v___x_3277_, 1, lean_box(0));
lean_closure_set(v___x_3277_, 2, v_a_3271_);
v___x_3278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3277_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3313_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3313_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3313_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3279_, v_e_3270_);
lean_dec(v_a_3279_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; 
lean_del_object(v___x_3281_);
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3285_ = lean_box(v_usedLetOnly_3267_);
v___x_3286_ = lean_box(v_skipConstInApp_3268_);
v___x_3287_ = lean_box(v_skipInstances_3269_);
lean_inc_ref(v_e_3270_);
v___f_3288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3288_, 0, v___x_3284_);
lean_closure_set(v___f_3288_, 1, v_pre_3265_);
lean_closure_set(v___f_3288_, 2, v_e_3270_);
lean_closure_set(v___f_3288_, 3, v_post_3266_);
lean_closure_set(v___f_3288_, 4, v___x_3285_);
lean_closure_set(v___f_3288_, 5, v___x_3286_);
lean_closure_set(v___f_3288_, 6, v___x_3287_);
v___x_3289_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3288_, v_a_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc_n(v_a_3290_, 2);
lean_dec_ref(v___x_3289_);
lean_inc(v_a_3271_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3291_, 0, v_a_3271_);
lean_closure_set(v___f_3291_, 1, v_e_3270_);
lean_closure_set(v___f_3291_, 2, v_a_3290_);
v___x_3292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3291_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; 
v_unused_3300_ = lean_ctor_get(v___x_3292_, 0);
lean_dec(v_unused_3300_);
v___x_3294_ = v___x_3292_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v___x_3292_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v_a_3290_);
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3290_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_a_3290_);
v_a_3301_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3292_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3292_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_dec_ref(v_e_3270_);
return v___x_3289_;
}
}
else
{
lean_object* v_val_3309_; lean_object* v___x_3311_; 
lean_dec_ref(v_e_3270_);
lean_dec_ref(v_post_3266_);
lean_dec_ref(v_pre_3265_);
v_val_3309_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_val_3309_);
lean_dec_ref(v___x_3283_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v_val_3309_);
v___x_3311_ = v___x_3281_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_val_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec_ref(v_e_3270_);
lean_dec_ref(v_post_3266_);
lean_dec_ref(v_pre_3265_);
v_a_3314_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3278_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3278_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3322_, lean_object* v_pre_3323_, lean_object* v_post_3324_, lean_object* v_usedLetOnly_3325_, lean_object* v_skipConstInApp_3326_, lean_object* v_skipInstances_3327_, lean_object* v_body_3328_, lean_object* v_x_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
uint8_t v_usedLetOnly_boxed_3336_; uint8_t v_skipConstInApp_boxed_3337_; uint8_t v_skipInstances_boxed_3338_; lean_object* v_res_3339_; 
v_usedLetOnly_boxed_3336_ = lean_unbox(v_usedLetOnly_3325_);
v_skipConstInApp_boxed_3337_ = lean_unbox(v_skipConstInApp_3326_);
v_skipInstances_boxed_3338_ = lean_unbox(v_skipInstances_3327_);
v_res_3339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3322_, v_pre_3323_, v_post_3324_, v_usedLetOnly_boxed_3336_, v_skipConstInApp_boxed_3337_, v_skipInstances_boxed_3338_, v_body_3328_, v_x_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3340_, lean_object* v_post_3341_, uint8_t v_usedLetOnly_3342_, uint8_t v_skipConstInApp_3343_, uint8_t v_skipInstances_3344_, lean_object* v_fvars_3345_, lean_object* v_e_3346_, lean_object* v_a_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
if (lean_obj_tag(v_e_3346_) == 7)
{
lean_object* v_binderName_3353_; lean_object* v_binderType_3354_; lean_object* v_body_3355_; uint8_t v_binderInfo_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_binderName_3353_ = lean_ctor_get(v_e_3346_, 0);
lean_inc(v_binderName_3353_);
v_binderType_3354_ = lean_ctor_get(v_e_3346_, 1);
lean_inc_ref(v_binderType_3354_);
v_body_3355_ = lean_ctor_get(v_e_3346_, 2);
lean_inc_ref(v_body_3355_);
v_binderInfo_3356_ = lean_ctor_get_uint8(v_e_3346_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3346_);
v___x_3357_ = lean_expr_instantiate_rev(v_binderType_3354_, v_fvars_3345_);
lean_dec_ref(v_binderType_3354_);
lean_inc_ref(v_post_3341_);
lean_inc_ref(v_pre_3340_);
v___x_3358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3340_, v_post_3341_, v_usedLetOnly_3342_, v_skipConstInApp_3343_, v_skipInstances_3344_, v___x_3357_, v_a_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___f_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = lean_box(v_usedLetOnly_3342_);
v___x_3361_ = lean_box(v_skipConstInApp_3343_);
v___x_3362_ = lean_box(v_skipInstances_3344_);
v___f_3363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3363_, 0, v_fvars_3345_);
lean_closure_set(v___f_3363_, 1, v_pre_3340_);
lean_closure_set(v___f_3363_, 2, v_post_3341_);
lean_closure_set(v___f_3363_, 3, v___x_3360_);
lean_closure_set(v___f_3363_, 4, v___x_3361_);
lean_closure_set(v___f_3363_, 5, v___x_3362_);
lean_closure_set(v___f_3363_, 6, v_body_3355_);
v___x_3364_ = 0;
v___x_3365_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3353_, v_binderInfo_3356_, v_a_3359_, v___f_3363_, v___x_3364_, v_a_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3365_;
}
else
{
lean_dec_ref(v_body_3355_);
lean_dec(v_binderName_3353_);
lean_dec_ref(v_fvars_3345_);
lean_dec_ref(v_post_3341_);
lean_dec_ref(v_pre_3340_);
return v___x_3358_;
}
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_expr_instantiate_rev(v_e_3346_, v_fvars_3345_);
lean_dec_ref(v_e_3346_);
lean_inc_ref(v_post_3341_);
lean_inc_ref(v_pre_3340_);
v___x_3367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3340_, v_post_3341_, v_usedLetOnly_3342_, v_skipConstInApp_3343_, v_skipInstances_3344_, v___x_3366_, v_a_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; uint8_t v___x_3369_; uint8_t v___x_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = 0;
v___x_3370_ = 1;
v___x_3371_ = 1;
v___x_3372_ = l_Lean_Meta_mkForallFVars(v_fvars_3345_, v_a_3368_, v___x_3369_, v_usedLetOnly_3342_, v___x_3370_, v___x_3371_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec_ref(v_fvars_3345_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref(v___x_3372_);
v___x_3374_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3340_, v_post_3341_, v_usedLetOnly_3342_, v_skipConstInApp_3343_, v_skipInstances_3344_, v_a_3373_, v_a_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3374_;
}
else
{
lean_dec_ref(v_post_3341_);
lean_dec_ref(v_pre_3340_);
return v___x_3372_;
}
}
else
{
lean_dec_ref(v_fvars_3345_);
lean_dec_ref(v_post_3341_);
lean_dec_ref(v_pre_3340_);
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3375_, lean_object* v_pre_3376_, lean_object* v_post_3377_, uint8_t v_usedLetOnly_3378_, uint8_t v_skipConstInApp_3379_, uint8_t v_skipInstances_3380_, lean_object* v_body_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_array_push(v_fvars_3375_, v_x_3382_);
v___x_3390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3376_, v_post_3377_, v_usedLetOnly_3378_, v_skipConstInApp_3379_, v_skipInstances_3380_, v___x_3389_, v_body_3381_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3391_, lean_object* v_post_3392_, lean_object* v_usedLetOnly_3393_, lean_object* v_skipConstInApp_3394_, lean_object* v_skipInstances_3395_, lean_object* v_e_3396_, lean_object* v_a_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v_usedLetOnly_boxed_3403_; uint8_t v_skipConstInApp_boxed_3404_; uint8_t v_skipInstances_boxed_3405_; lean_object* v_res_3406_; 
v_usedLetOnly_boxed_3403_ = lean_unbox(v_usedLetOnly_3393_);
v_skipConstInApp_boxed_3404_ = lean_unbox(v_skipConstInApp_3394_);
v_skipInstances_boxed_3405_ = lean_unbox(v_skipInstances_3395_);
v_res_3406_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3391_, v_post_3392_, v_usedLetOnly_boxed_3403_, v_skipConstInApp_boxed_3404_, v_skipInstances_boxed_3405_, v_e_3396_, v_a_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v_a_3397_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3407_, lean_object* v_post_3408_, lean_object* v_usedLetOnly_3409_, lean_object* v_skipConstInApp_3410_, lean_object* v_skipInstances_3411_, lean_object* v_sz_3412_, lean_object* v_i_3413_, lean_object* v_bs_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v_usedLetOnly_boxed_3421_; uint8_t v_skipConstInApp_boxed_3422_; uint8_t v_skipInstances_boxed_3423_; size_t v_sz_boxed_3424_; size_t v_i_boxed_3425_; lean_object* v_res_3426_; 
v_usedLetOnly_boxed_3421_ = lean_unbox(v_usedLetOnly_3409_);
v_skipConstInApp_boxed_3422_ = lean_unbox(v_skipConstInApp_3410_);
v_skipInstances_boxed_3423_ = lean_unbox(v_skipInstances_3411_);
v_sz_boxed_3424_ = lean_unbox_usize(v_sz_3412_);
lean_dec(v_sz_3412_);
v_i_boxed_3425_ = lean_unbox_usize(v_i_3413_);
lean_dec(v_i_3413_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3407_, v_post_3408_, v_usedLetOnly_boxed_3421_, v_skipConstInApp_boxed_3422_, v_skipInstances_boxed_3423_, v_sz_boxed_3424_, v_i_boxed_3425_, v_bs_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3427_, lean_object* v_post_3428_, lean_object* v_usedLetOnly_3429_, lean_object* v_skipConstInApp_3430_, lean_object* v_skipInstances_3431_, lean_object* v_e_3432_, lean_object* v_a_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v_usedLetOnly_boxed_3439_; uint8_t v_skipConstInApp_boxed_3440_; uint8_t v_skipInstances_boxed_3441_; lean_object* v_res_3442_; 
v_usedLetOnly_boxed_3439_ = lean_unbox(v_usedLetOnly_3429_);
v_skipConstInApp_boxed_3440_ = lean_unbox(v_skipConstInApp_3430_);
v_skipInstances_boxed_3441_ = lean_unbox(v_skipInstances_3431_);
v_res_3442_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3427_, v_post_3428_, v_usedLetOnly_boxed_3439_, v_skipConstInApp_boxed_3440_, v_skipInstances_boxed_3441_, v_e_3432_, v_a_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v_a_3433_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3443_, lean_object* v_post_3444_, lean_object* v_usedLetOnly_3445_, lean_object* v_skipConstInApp_3446_, lean_object* v_skipInstances_3447_, lean_object* v_fvars_3448_, lean_object* v_e_3449_, lean_object* v_a_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v_usedLetOnly_boxed_3456_; uint8_t v_skipConstInApp_boxed_3457_; uint8_t v_skipInstances_boxed_3458_; lean_object* v_res_3459_; 
v_usedLetOnly_boxed_3456_ = lean_unbox(v_usedLetOnly_3445_);
v_skipConstInApp_boxed_3457_ = lean_unbox(v_skipConstInApp_3446_);
v_skipInstances_boxed_3458_ = lean_unbox(v_skipInstances_3447_);
v_res_3459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3443_, v_post_3444_, v_usedLetOnly_boxed_3456_, v_skipConstInApp_boxed_3457_, v_skipInstances_boxed_3458_, v_fvars_3448_, v_e_3449_, v_a_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v_a_3450_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3460_, lean_object* v_post_3461_, lean_object* v_usedLetOnly_3462_, lean_object* v_skipConstInApp_3463_, lean_object* v_skipInstances_3464_, lean_object* v_fvars_3465_, lean_object* v_e_3466_, lean_object* v_a_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
uint8_t v_usedLetOnly_boxed_3473_; uint8_t v_skipConstInApp_boxed_3474_; uint8_t v_skipInstances_boxed_3475_; lean_object* v_res_3476_; 
v_usedLetOnly_boxed_3473_ = lean_unbox(v_usedLetOnly_3462_);
v_skipConstInApp_boxed_3474_ = lean_unbox(v_skipConstInApp_3463_);
v_skipInstances_boxed_3475_ = lean_unbox(v_skipInstances_3464_);
v_res_3476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3460_, v_post_3461_, v_usedLetOnly_boxed_3473_, v_skipConstInApp_boxed_3474_, v_skipInstances_boxed_3475_, v_fvars_3465_, v_e_3466_, v_a_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v_a_3467_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3477_, lean_object* v_post_3478_, lean_object* v_usedLetOnly_3479_, lean_object* v_skipConstInApp_3480_, lean_object* v_skipInstances_3481_, lean_object* v_fvars_3482_, lean_object* v_e_3483_, lean_object* v_a_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
uint8_t v_usedLetOnly_boxed_3490_; uint8_t v_skipConstInApp_boxed_3491_; uint8_t v_skipInstances_boxed_3492_; lean_object* v_res_3493_; 
v_usedLetOnly_boxed_3490_ = lean_unbox(v_usedLetOnly_3479_);
v_skipConstInApp_boxed_3491_ = lean_unbox(v_skipConstInApp_3480_);
v_skipInstances_boxed_3492_ = lean_unbox(v_skipInstances_3481_);
v_res_3493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3477_, v_post_3478_, v_usedLetOnly_boxed_3490_, v_skipConstInApp_boxed_3491_, v_skipInstances_boxed_3492_, v_fvars_3482_, v_e_3483_, v_a_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v_a_3484_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3494_, lean_object* v___x_3495_, lean_object* v_pre_3496_, lean_object* v_post_3497_, lean_object* v_usedLetOnly_3498_, lean_object* v_skipConstInApp_3499_, lean_object* v_skipInstances_3500_, lean_object* v_a_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
uint8_t v_usedLetOnly_boxed_3509_; uint8_t v_skipConstInApp_boxed_3510_; uint8_t v_skipInstances_boxed_3511_; lean_object* v_res_3512_; 
v_usedLetOnly_boxed_3509_ = lean_unbox(v_usedLetOnly_3498_);
v_skipConstInApp_boxed_3510_ = lean_unbox(v_skipConstInApp_3499_);
v_skipInstances_boxed_3511_ = lean_unbox(v_skipInstances_3500_);
v_res_3512_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3494_, v___x_3495_, v_pre_3496_, v_post_3497_, v_usedLetOnly_boxed_3509_, v_skipConstInApp_boxed_3510_, v_skipInstances_boxed_3511_, v_a_3501_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___x_3495_);
lean_dec(v_upperBound_3494_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3513_, lean_object* v_pre_3514_, lean_object* v_post_3515_, lean_object* v_usedLetOnly_3516_, lean_object* v_skipConstInApp_3517_, lean_object* v_x_3518_, lean_object* v_x_3519_, lean_object* v_x_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v_skipInstances_boxed_3527_; uint8_t v_usedLetOnly_boxed_3528_; uint8_t v_skipConstInApp_boxed_3529_; lean_object* v_res_3530_; 
v_skipInstances_boxed_3527_ = lean_unbox(v_skipInstances_3513_);
v_usedLetOnly_boxed_3528_ = lean_unbox(v_usedLetOnly_3516_);
v_skipConstInApp_boxed_3529_ = lean_unbox(v_skipConstInApp_3517_);
v_res_3530_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3527_, v_pre_3514_, v_post_3515_, v_usedLetOnly_boxed_3528_, v_skipConstInApp_boxed_3529_, v_x_3518_, v_x_3519_, v_x_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3531_ = lean_box(0);
v___x_3532_ = lean_unsigned_to_nat(16u);
v___x_3533_ = lean_mk_array(v___x_3532_, v___x_3531_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
lean_ctor_set(v___x_3536_, 1, v___x_3534_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3538_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3538_, 0, lean_box(0));
lean_closure_set(v___x_3538_, 1, lean_box(0));
lean_closure_set(v___x_3538_, 2, v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3539_, lean_object* v_pre_3540_, lean_object* v_post_3541_, uint8_t v_usedLetOnly_3542_, uint8_t v_skipConstInApp_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_a_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; 
v___x_3549_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3550_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3549_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = 0;
v___x_3553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3540_, v_post_3541_, v_usedLetOnly_3542_, v_skipConstInApp_3543_, v___x_3552_, v_input_3539_, v_a_3551_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref(v___x_3553_);
v___x_3555_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3555_, 0, lean_box(0));
lean_closure_set(v___x_3555_, 1, lean_box(0));
lean_closure_set(v___x_3555_, 2, v_a_3551_);
v___x_3556_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3555_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3563_ == 0)
{
lean_object* v_unused_3564_; 
v_unused_3564_ = lean_ctor_get(v___x_3556_, 0);
lean_dec(v_unused_3564_);
v___x_3558_ = v___x_3556_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_dec(v___x_3556_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v_a_3554_);
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3554_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
else
{
lean_dec(v_a_3551_);
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3565_, lean_object* v_pre_3566_, lean_object* v_post_3567_, lean_object* v_usedLetOnly_3568_, lean_object* v_skipConstInApp_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_usedLetOnly_boxed_3575_; uint8_t v_skipConstInApp_boxed_3576_; lean_object* v_res_3577_; 
v_usedLetOnly_boxed_3575_ = lean_unbox(v_usedLetOnly_3568_);
v_skipConstInApp_boxed_3576_ = lean_unbox(v_skipConstInApp_3569_);
v_res_3577_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3565_, v_pre_3566_, v_post_3567_, v_usedLetOnly_boxed_3575_, v_skipConstInApp_boxed_3576_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3579_, lean_object* v_p_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___x_3586_; lean_object* v_a_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; uint8_t v___x_3590_; lean_object* v___x_3591_; 
v___x_3586_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3579_, v_a_3582_);
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
v___f_3588_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3589_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3589_, 0, v_p_3580_);
v___x_3590_ = 0;
v___x_3591_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3587_, v___f_3588_, v___f_3589_, v___x_3590_, v___x_3590_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3592_, lean_object* v_p_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Meta_etaStructReduce(v_e_3592_, v_p_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3600_, lean_object* v___x_3601_, lean_object* v_pre_3602_, lean_object* v_post_3603_, uint8_t v_usedLetOnly_3604_, uint8_t v_skipConstInApp_3605_, uint8_t v_skipInstances_3606_, lean_object* v___x_3607_, lean_object* v_inst_3608_, lean_object* v_R_3609_, lean_object* v_a_3610_, lean_object* v_b_3611_, lean_object* v_c_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3600_, v___x_3601_, v_pre_3602_, v_post_3603_, v_usedLetOnly_3604_, v_skipConstInApp_3605_, v_skipInstances_3606_, v_a_3610_, v_b_3611_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3620_ = _args[0];
lean_object* v___x_3621_ = _args[1];
lean_object* v_pre_3622_ = _args[2];
lean_object* v_post_3623_ = _args[3];
lean_object* v_usedLetOnly_3624_ = _args[4];
lean_object* v_skipConstInApp_3625_ = _args[5];
lean_object* v_skipInstances_3626_ = _args[6];
lean_object* v___x_3627_ = _args[7];
lean_object* v_inst_3628_ = _args[8];
lean_object* v_R_3629_ = _args[9];
lean_object* v_a_3630_ = _args[10];
lean_object* v_b_3631_ = _args[11];
lean_object* v_c_3632_ = _args[12];
lean_object* v___y_3633_ = _args[13];
lean_object* v___y_3634_ = _args[14];
lean_object* v___y_3635_ = _args[15];
lean_object* v___y_3636_ = _args[16];
lean_object* v___y_3637_ = _args[17];
lean_object* v___y_3638_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3639_; uint8_t v_skipConstInApp_boxed_3640_; uint8_t v_skipInstances_boxed_3641_; lean_object* v_res_3642_; 
v_usedLetOnly_boxed_3639_ = lean_unbox(v_usedLetOnly_3624_);
v_skipConstInApp_boxed_3640_ = lean_unbox(v_skipConstInApp_3625_);
v_skipInstances_boxed_3641_ = lean_unbox(v_skipInstances_3626_);
v_res_3642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3620_, v___x_3621_, v_pre_3622_, v_post_3623_, v_usedLetOnly_boxed_3639_, v_skipConstInApp_boxed_3640_, v_skipInstances_boxed_3641_, v___x_3627_, v_inst_3628_, v_R_3629_, v_a_3630_, v_b_3631_, v_c_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec(v___x_3627_);
lean_dec_ref(v___x_3621_);
lean_dec(v_upperBound_3620_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3643_, lean_object* v_m_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3644_, v_a_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3647_, lean_object* v_m_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3647_, v_m_3648_, v_a_3649_);
lean_dec_ref(v_a_3649_);
lean_dec_ref(v_m_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3651_, lean_object* v_name_3652_, uint8_t v_bi_3653_, lean_object* v_type_3654_, lean_object* v_k_3655_, uint8_t v_kind_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3652_, v_bi_3653_, v_type_3654_, v_k_3655_, v_kind_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_name_3665_, lean_object* v_bi_3666_, lean_object* v_type_3667_, lean_object* v_k_3668_, lean_object* v_kind_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_bi_boxed_3676_; uint8_t v_kind_boxed_3677_; lean_object* v_res_3678_; 
v_bi_boxed_3676_ = lean_unbox(v_bi_3666_);
v_kind_boxed_3677_ = lean_unbox(v_kind_3669_);
v_res_3678_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3664_, v_name_3665_, v_bi_boxed_3676_, v_type_3667_, v_k_3668_, v_kind_boxed_3677_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3679_, lean_object* v_name_3680_, lean_object* v_type_3681_, lean_object* v_val_3682_, lean_object* v_k_3683_, uint8_t v_nondep_3684_, uint8_t v_kind_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3680_, v_type_3681_, v_val_3682_, v_k_3683_, v_nondep_3684_, v_kind_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_name_3694_, lean_object* v_type_3695_, lean_object* v_val_3696_, lean_object* v_k_3697_, lean_object* v_nondep_3698_, lean_object* v_kind_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
uint8_t v_nondep_boxed_3706_; uint8_t v_kind_boxed_3707_; lean_object* v_res_3708_; 
v_nondep_boxed_3706_ = lean_unbox(v_nondep_3698_);
v_kind_boxed_3707_ = lean_unbox(v_kind_3699_);
v_res_3708_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3693_, v_name_3694_, v_type_3695_, v_val_3696_, v_k_3697_, v_nondep_boxed_3706_, v_kind_boxed_3707_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3709_, lean_object* v_ref_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3710_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3717_, lean_object* v_ref_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3717_, v_ref_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3725_, lean_object* v_x_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3734_, lean_object* v_x_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3734_, v_x_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3743_, lean_object* v_m_3744_, lean_object* v_a_3745_, lean_object* v_b_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3744_, v_a_3745_, v_b_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3748_, lean_object* v_a_3749_, lean_object* v_x_3750_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3749_, v_x_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3752_, lean_object* v_a_3753_, lean_object* v_x_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3752_, v_a_3753_, v_x_3754_);
lean_dec(v_x_3754_);
lean_dec_ref(v_a_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3756_, lean_object* v_a_3757_, lean_object* v_x_3758_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3757_, v_x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3760_, lean_object* v_a_3761_, lean_object* v_x_3762_){
_start:
{
uint8_t v_res_3763_; lean_object* v_r_3764_; 
v_res_3763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3760_, v_a_3761_, v_x_3762_);
lean_dec(v_x_3762_);
lean_dec_ref(v_a_3761_);
v_r_3764_ = lean_box(v_res_3763_);
return v_r_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3765_, lean_object* v_data_3766_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3768_, lean_object* v_a_3769_, lean_object* v_b_3770_, lean_object* v_x_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3769_, v_b_3770_, v_x_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3773_, lean_object* v_i_3774_, lean_object* v_source_3775_, lean_object* v_target_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3774_, v_source_3775_, v_target_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3778_, lean_object* v_x_3779_, lean_object* v_x_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3779_, v_x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3782_, lean_object* v_inst_3783_, lean_object* v_toBind_3784_, lean_object* v___f_3785_, lean_object* v_____do__lift_3786_){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3787_, 0, v_____do__lift_3786_);
lean_closure_set(v___x_3787_, 1, v_binderType_3782_);
v___x_3788_ = lean_apply_2(v_inst_3783_, lean_box(0), v___x_3787_);
v___x_3789_ = lean_apply_4(v_toBind_3784_, lean_box(0), lean_box(0), v___x_3788_, v___f_3785_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3790_, lean_object* v_usedFields_3791_, lean_object* v_binderName_3792_, lean_object* v_body_3793_, lean_object* v_val_3794_, lean_object* v_inst_3795_, lean_object* v_inst_3796_, lean_object* v_fieldVal_x3f_3797_, lean_object* v_____do__lift_3798_){
_start:
{
uint8_t v_____do__lift_469__boxed_3799_; lean_object* v_res_3800_; 
v_____do__lift_469__boxed_3799_ = lean_unbox(v_____do__lift_3798_);
v_res_3800_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3790_, v_usedFields_3791_, v_binderName_3792_, v_body_3793_, v_val_3794_, v_inst_3795_, v_inst_3796_, v_fieldVal_x3f_3797_, v_____do__lift_469__boxed_3799_);
lean_dec_ref(v_val_3794_);
lean_dec_ref(v_body_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3801_, lean_object* v_usedFields_3802_, lean_object* v_binderName_3803_, lean_object* v_body_3804_, lean_object* v_inst_3805_, lean_object* v_inst_3806_, lean_object* v_fieldVal_x3f_3807_, lean_object* v_binderType_3808_, lean_object* v_toBind_3809_, lean_object* v_____x_3810_){
_start:
{
if (lean_obj_tag(v_____x_3810_) == 1)
{
lean_object* v_val_3811_; lean_object* v___f_3812_; lean_object* v___f_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_val_3811_ = lean_ctor_get(v_____x_3810_, 0);
lean_inc_n(v_val_3811_, 2);
lean_dec_ref(v_____x_3810_);
lean_inc_n(v_inst_3806_, 2);
v___f_3812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3812_, 0, v_toPure_3801_);
lean_closure_set(v___f_3812_, 1, v_usedFields_3802_);
lean_closure_set(v___f_3812_, 2, v_binderName_3803_);
lean_closure_set(v___f_3812_, 3, v_body_3804_);
lean_closure_set(v___f_3812_, 4, v_val_3811_);
lean_closure_set(v___f_3812_, 5, v_inst_3805_);
lean_closure_set(v___f_3812_, 6, v_inst_3806_);
lean_closure_set(v___f_3812_, 7, v_fieldVal_x3f_3807_);
lean_inc(v_toBind_3809_);
v___f_3813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3813_, 0, v_binderType_3808_);
lean_closure_set(v___f_3813_, 1, v_inst_3806_);
lean_closure_set(v___f_3813_, 2, v_toBind_3809_);
lean_closure_set(v___f_3813_, 3, v___f_3812_);
v___x_3814_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3814_, 0, v_val_3811_);
v___x_3815_ = lean_apply_2(v_inst_3806_, lean_box(0), v___x_3814_);
v___x_3816_ = lean_apply_4(v_toBind_3809_, lean_box(0), lean_box(0), v___x_3815_, v___f_3813_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v_____x_3810_);
lean_dec(v_toBind_3809_);
lean_dec_ref(v_binderType_3808_);
lean_dec(v_fieldVal_x3f_3807_);
lean_dec(v_inst_3806_);
lean_dec_ref(v_inst_3805_);
lean_dec_ref(v_body_3804_);
lean_dec(v_binderName_3803_);
lean_dec(v_usedFields_3802_);
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_apply_2(v_toPure_3801_, lean_box(0), v___x_3817_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3822_, lean_object* v_inst_3823_, lean_object* v_fieldVal_x3f_3824_, lean_object* v_usedFields_3825_, lean_object* v_e_3826_){
_start:
{
lean_object* v_toApplicative_3827_; lean_object* v_toBind_3828_; lean_object* v_toPure_3829_; 
v_toApplicative_3827_ = lean_ctor_get(v_inst_3822_, 0);
v_toBind_3828_ = lean_ctor_get(v_inst_3822_, 1);
v_toPure_3829_ = lean_ctor_get(v_toApplicative_3827_, 1);
lean_inc(v_toPure_3829_);
if (lean_obj_tag(v_e_3826_) == 6)
{
lean_object* v_binderName_3834_; lean_object* v_binderType_3835_; lean_object* v_body_3836_; lean_object* v___f_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_inc_n(v_toBind_3828_, 2);
v_binderName_3834_ = lean_ctor_get(v_e_3826_, 0);
lean_inc_n(v_binderName_3834_, 2);
v_binderType_3835_ = lean_ctor_get(v_e_3826_, 1);
lean_inc_ref(v_binderType_3835_);
v_body_3836_ = lean_ctor_get(v_e_3826_, 2);
lean_inc_ref(v_body_3836_);
lean_dec_ref(v_e_3826_);
lean_inc(v_fieldVal_x3f_3824_);
v___f_3837_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3837_, 0, v_toPure_3829_);
lean_closure_set(v___f_3837_, 1, v_usedFields_3825_);
lean_closure_set(v___f_3837_, 2, v_binderName_3834_);
lean_closure_set(v___f_3837_, 3, v_body_3836_);
lean_closure_set(v___f_3837_, 4, v_inst_3822_);
lean_closure_set(v___f_3837_, 5, v_inst_3823_);
lean_closure_set(v___f_3837_, 6, v_fieldVal_x3f_3824_);
lean_closure_set(v___f_3837_, 7, v_binderType_3835_);
lean_closure_set(v___f_3837_, 8, v_toBind_3828_);
v___x_3838_ = lean_apply_1(v_fieldVal_x3f_3824_, v_binderName_3834_);
v___x_3839_ = lean_apply_4(v_toBind_3828_, lean_box(0), lean_box(0), v___x_3838_, v___f_3837_);
return v___x_3839_;
}
else
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v_fieldVal_x3f_3824_);
lean_dec(v_inst_3823_);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_inst_3822_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; lean_object* v_unused_3858_; 
v_unused_3857_ = lean_ctor_get(v_inst_3822_, 1);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_inst_3822_, 0);
lean_dec(v_unused_3858_);
v___x_3841_ = v_inst_3822_;
v_isShared_3842_ = v_isSharedCheck_3856_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_inst_3822_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3856_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; uint8_t v___x_3844_; 
lean_inc_ref(v_e_3826_);
v___x_3843_ = l_Lean_Expr_cleanupAnnotations(v_e_3826_);
v___x_3844_ = l_Lean_Expr_isApp(v___x_3843_);
if (v___x_3844_ == 0)
{
lean_dec_ref(v___x_3843_);
lean_del_object(v___x_3841_);
goto v___jp_3830_;
}
else
{
lean_object* v_arg_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_arg_3845_ = lean_ctor_get(v___x_3843_, 1);
lean_inc_ref(v_arg_3845_);
v___x_3846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3843_);
v___x_3847_ = l_Lean_Expr_isApp(v___x_3846_);
if (v___x_3847_ == 0)
{
lean_dec_ref(v___x_3846_);
lean_dec_ref(v_arg_3845_);
lean_del_object(v___x_3841_);
goto v___jp_3830_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v___x_3848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3846_);
v___x_3849_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3850_ = l_Lean_Expr_isConstOf(v___x_3848_, v___x_3849_);
lean_dec_ref(v___x_3848_);
if (v___x_3850_ == 0)
{
lean_dec_ref(v_arg_3845_);
lean_del_object(v___x_3841_);
goto v___jp_3830_;
}
else
{
lean_object* v___x_3852_; 
lean_dec_ref(v_e_3826_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v_arg_3845_);
lean_ctor_set(v___x_3841_, 0, v_usedFields_3825_);
v___x_3852_ = v___x_3841_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_usedFields_3825_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_arg_3845_);
v___x_3852_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
v___x_3854_ = lean_apply_2(v_toPure_3829_, lean_box(0), v___x_3853_);
return v___x_3854_;
}
}
}
}
}
}
v___jp_3830_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v_usedFields_3825_);
lean_ctor_set(v___x_3831_, 1, v_e_3826_);
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
v___x_3833_ = lean_apply_2(v_toPure_3829_, lean_box(0), v___x_3832_);
return v___x_3833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3859_, lean_object* v_usedFields_3860_, lean_object* v_binderName_3861_, lean_object* v_body_3862_, lean_object* v_val_3863_, lean_object* v_inst_3864_, lean_object* v_inst_3865_, lean_object* v_fieldVal_x3f_3866_, uint8_t v_____do__lift_3867_){
_start:
{
if (v_____do__lift_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_dec(v_fieldVal_x3f_3866_);
lean_dec(v_inst_3865_);
lean_dec_ref(v_inst_3864_);
lean_dec(v_binderName_3861_);
lean_dec(v_usedFields_3860_);
v___x_3868_ = lean_box(0);
v___x_3869_ = lean_apply_2(v_toPure_3859_, lean_box(0), v___x_3868_);
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec(v_toPure_3859_);
v___x_3870_ = l_Lean_NameSet_insert(v_usedFields_3860_, v_binderName_3861_);
v___x_3871_ = lean_expr_instantiate1(v_body_3862_, v_val_3863_);
v___x_3872_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3864_, v_inst_3865_, v_fieldVal_x3f_3866_, v___x_3870_, v___x_3871_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3873_, lean_object* v_inst_3874_, lean_object* v_inst_3875_, lean_object* v_fieldVal_x3f_3876_, lean_object* v_usedFields_3877_, lean_object* v_e_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3874_, v_inst_3875_, v_fieldVal_x3f_3876_, v_usedFields_3877_, v_e_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3880_, lean_object* v_inst_3881_, lean_object* v_fieldVal_x3f_3882_, lean_object* v_toPure_3883_, lean_object* v_____s_3884_){
_start:
{
lean_object* v_fst_3885_; 
v_fst_3885_ = lean_ctor_get(v_____s_3884_, 0);
if (lean_obj_tag(v_fst_3885_) == 0)
{
lean_object* v_snd_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
lean_dec(v_toPure_3883_);
v_snd_3886_ = lean_ctor_get(v_____s_3884_, 1);
lean_inc(v_snd_3886_);
lean_dec_ref(v_____s_3884_);
v___x_3887_ = l_Lean_NameSet_empty;
v___x_3888_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3880_, v_inst_3881_, v_fieldVal_x3f_3882_, v___x_3887_, v_snd_3886_);
return v___x_3888_;
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3890_; 
lean_inc_ref(v_fst_3885_);
lean_dec_ref(v_____s_3884_);
lean_dec(v_fieldVal_x3f_3882_);
lean_dec(v_inst_3881_);
lean_dec_ref(v_inst_3880_);
v_val_3889_ = lean_ctor_get(v_fst_3885_, 0);
lean_inc(v_val_3889_);
lean_dec_ref(v_fst_3885_);
v___x_3890_ = lean_apply_2(v_toPure_3883_, lean_box(0), v_val_3889_);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3891_, lean_object* v_a_3892_, lean_object* v___x_3893_, lean_object* v_toPure_3894_, lean_object* v_____r_3895_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3896_ = lean_expr_instantiate1(v_body_3891_, v_a_3892_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3893_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
v___x_3899_ = lean_apply_2(v_toPure_3894_, lean_box(0), v___x_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3900_, lean_object* v_a_3901_, lean_object* v___x_3902_, lean_object* v_toPure_3903_, lean_object* v_____r_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3900_, v_a_3901_, v___x_3902_, v_toPure_3903_, v_____r_3904_);
lean_dec_ref(v_a_3901_);
lean_dec_ref(v_body_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3908_, lean_object* v_toPure_3909_, lean_object* v___f_3910_, uint8_t v_____do__lift_3911_){
_start:
{
if (v_____do__lift_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec(v___f_3910_);
v___x_3912_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v_snd_3908_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = lean_apply_2(v_toPure_3909_, lean_box(0), v___x_3914_);
return v___x_3915_;
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec(v_toPure_3909_);
lean_dec(v_snd_3908_);
v___x_3916_ = lean_box(0);
v___x_3917_ = lean_apply_1(v___f_3910_, v___x_3916_);
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3918_, lean_object* v_toPure_3919_, lean_object* v___f_3920_, lean_object* v_____do__lift_3921_){
_start:
{
uint8_t v_____do__lift_852__boxed_3922_; lean_object* v_res_3923_; 
v_____do__lift_852__boxed_3922_ = lean_unbox(v_____do__lift_3921_);
v_res_3923_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3918_, v_toPure_3919_, v___f_3920_, v_____do__lift_852__boxed_3922_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3924_, lean_object* v_inst_3925_, lean_object* v_toBind_3926_, lean_object* v___f_3927_, lean_object* v_____do__lift_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3929_, 0, v_____do__lift_3928_);
lean_closure_set(v___x_3929_, 1, v_binderType_3924_);
v___x_3930_ = lean_apply_2(v_inst_3925_, lean_box(0), v___x_3929_);
v___x_3931_ = lean_apply_4(v_toBind_3926_, lean_box(0), lean_box(0), v___x_3930_, v___f_3927_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3932_, lean_object* v_toPure_3933_, lean_object* v_levels_x3f_3934_, uint8_t v___x_3935_, lean_object* v_inst_3936_, lean_object* v_toBind_3937_, lean_object* v_a_3938_, lean_object* v_x_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_snd_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3962_; 
v_snd_3941_ = lean_ctor_get(v___y_3940_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___y_3940_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v___y_3940_, 0);
lean_dec(v_unused_3963_);
v___x_3943_ = v___y_3940_;
v_isShared_3944_ = v_isSharedCheck_3962_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_snd_3941_);
lean_dec(v___y_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3962_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
if (lean_obj_tag(v_snd_3941_) == 6)
{
lean_object* v_binderType_3945_; lean_object* v_body_3946_; lean_object* v___f_3947_; 
lean_del_object(v___x_3943_);
v_binderType_3945_ = lean_ctor_get(v_snd_3941_, 1);
lean_inc_ref(v_binderType_3945_);
v_body_3946_ = lean_ctor_get(v_snd_3941_, 2);
lean_inc(v_toPure_3933_);
lean_inc(v___x_3932_);
lean_inc_ref(v_a_3938_);
lean_inc_ref(v_body_3946_);
v___f_3947_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3947_, 0, v_body_3946_);
lean_closure_set(v___f_3947_, 1, v_a_3938_);
lean_closure_set(v___f_3947_, 2, v___x_3932_);
lean_closure_set(v___f_3947_, 3, v_toPure_3933_);
if (lean_obj_tag(v_levels_x3f_3934_) == 0)
{
if (v___x_3935_ == 0)
{
lean_inc_ref(v_body_3946_);
lean_dec_ref(v___f_3947_);
lean_dec_ref(v_binderType_3945_);
lean_dec_ref(v_snd_3941_);
lean_dec(v_toBind_3937_);
lean_dec(v_inst_3936_);
goto v___jp_3948_;
}
else
{
lean_object* v___f_3951_; lean_object* v___f_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v___x_3932_);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3951_, 0, v_snd_3941_);
lean_closure_set(v___f_3951_, 1, v_toPure_3933_);
lean_closure_set(v___f_3951_, 2, v___f_3947_);
lean_inc(v_toBind_3937_);
lean_inc(v_inst_3936_);
v___f_3952_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3952_, 0, v_binderType_3945_);
lean_closure_set(v___f_3952_, 1, v_inst_3936_);
lean_closure_set(v___f_3952_, 2, v_toBind_3937_);
lean_closure_set(v___f_3952_, 3, v___f_3951_);
v___x_3953_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3953_, 0, v_a_3938_);
v___x_3954_ = lean_apply_2(v_inst_3936_, lean_box(0), v___x_3953_);
v___x_3955_ = lean_apply_4(v_toBind_3937_, lean_box(0), lean_box(0), v___x_3954_, v___f_3952_);
return v___x_3955_;
}
}
else
{
lean_inc_ref(v_body_3946_);
lean_dec_ref(v___f_3947_);
lean_dec_ref(v_binderType_3945_);
lean_dec_ref(v_snd_3941_);
lean_dec(v_toBind_3937_);
lean_dec(v_inst_3936_);
goto v___jp_3948_;
}
v___jp_3948_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_box(0);
v___x_3950_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3946_, v_a_3938_, v___x_3932_, v_toPure_3933_, v___x_3949_);
lean_dec_ref(v_a_3938_);
lean_dec_ref(v_body_3946_);
return v___x_3950_;
}
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
lean_dec_ref(v_a_3938_);
lean_dec(v_toBind_3937_);
lean_dec(v_inst_3936_);
lean_dec(v___x_3932_);
v___x_3956_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_3956_);
v___x_3958_ = v___x_3943_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_snd_3941_);
v___x_3958_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
v___x_3960_ = lean_apply_2(v_toPure_3933_, lean_box(0), v___x_3959_);
return v___x_3960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3964_, lean_object* v_toPure_3965_, lean_object* v_levels_x3f_3966_, lean_object* v___x_3967_, lean_object* v_inst_3968_, lean_object* v_toBind_3969_, lean_object* v_a_3970_, lean_object* v_x_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v___x_888__boxed_3973_; lean_object* v_res_3974_; 
v___x_888__boxed_3973_ = lean_unbox(v___x_3967_);
v_res_3974_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3964_, v_toPure_3965_, v_levels_x3f_3966_, v___x_888__boxed_3973_, v_inst_3968_, v_toBind_3969_, v_a_3970_, v_x_3971_, v___y_3972_);
lean_dec(v_levels_x3f_3966_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3975_, lean_object* v_levels_x3f_3976_, uint8_t v___x_3977_, lean_object* v_inst_3978_, lean_object* v_toBind_3979_, lean_object* v_params_3980_, lean_object* v_inst_3981_, lean_object* v___f_3982_, lean_object* v_val_3983_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___f_3986_; lean_object* v___x_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = lean_box(v___x_3977_);
lean_inc(v_toBind_3979_);
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_3986_, 0, v___x_3984_);
lean_closure_set(v___f_3986_, 1, v_toPure_3975_);
lean_closure_set(v___f_3986_, 2, v_levels_x3f_3976_);
lean_closure_set(v___f_3986_, 3, v___x_3985_);
lean_closure_set(v___f_3986_, 4, v_inst_3978_);
lean_closure_set(v___f_3986_, 5, v_toBind_3979_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3984_);
lean_ctor_set(v___x_3987_, 1, v_val_3983_);
v_sz_3988_ = lean_array_size(v_params_3980_);
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3981_, v_params_3980_, v___f_3986_, v_sz_3988_, v___x_3989_, v___x_3987_);
v___x_3991_ = lean_apply_4(v_toBind_3979_, lean_box(0), lean_box(0), v___x_3990_, v___f_3982_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v_toPure_3992_, lean_object* v_levels_x3f_3993_, lean_object* v___x_3994_, lean_object* v_inst_3995_, lean_object* v_toBind_3996_, lean_object* v_params_3997_, lean_object* v_inst_3998_, lean_object* v___f_3999_, lean_object* v_val_4000_){
_start:
{
uint8_t v___x_950__boxed_4001_; lean_object* v_res_4002_; 
v___x_950__boxed_4001_ = lean_unbox(v___x_3994_);
v_res_4002_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v_toPure_3992_, v_levels_x3f_3993_, v___x_950__boxed_4001_, v_inst_3995_, v_toBind_3996_, v_params_3997_, v_inst_3998_, v___f_3999_, v_val_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4003_, lean_object* v_us_4004_, uint8_t v___x_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4003_, v_us_4004_, v___x_4005_, v___y_4008_, v___y_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4012_, lean_object* v_us_4013_, lean_object* v___x_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
uint8_t v___x_976__boxed_4020_; lean_object* v_res_4021_; 
v___x_976__boxed_4020_ = lean_unbox(v___x_4014_);
v_res_4021_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4012_, v_us_4013_, v___x_976__boxed_4020_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec_ref(v_cinfo_4012_);
return v_res_4021_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4025_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4026_ = lean_unsigned_to_nat(2u);
v___x_4027_ = lean_unsigned_to_nat(202u);
v___x_4028_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4029_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4030_ = l_mkPanicMessageWithDecl(v___x_4029_, v___x_4028_, v___x_4027_, v___x_4026_, v___x_4025_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4031_, lean_object* v_inst_4032_, lean_object* v_toPure_4033_, lean_object* v_levels_x3f_4034_, lean_object* v_inst_4035_, lean_object* v_toBind_4036_, lean_object* v_params_4037_, lean_object* v___f_4038_, lean_object* v_us_4039_){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v___x_4040_ = l_List_lengthTR___redArg(v_us_4039_);
v___x_4041_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4031_);
v___x_4042_ = l_List_lengthTR___redArg(v___x_4041_);
lean_dec(v___x_4041_);
v___x_4043_ = lean_nat_dec_eq(v___x_4040_, v___x_4042_);
lean_dec(v___x_4042_);
lean_dec(v___x_4040_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec(v_us_4039_);
lean_dec(v___f_4038_);
lean_dec_ref(v_params_4037_);
lean_dec(v_toBind_4036_);
lean_dec(v_inst_4035_);
lean_dec(v_levels_x3f_4034_);
lean_dec(v_toPure_4033_);
lean_dec_ref(v_cinfo_4031_);
v___x_4044_ = lean_box(0);
v___x_4045_ = l_instInhabitedOfMonad___redArg(v_inst_4032_, v___x_4044_);
v___x_4046_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4047_ = l_panic___redArg(v___x_4045_, v___x_4046_);
lean_dec(v___x_4045_);
return v___x_4047_;
}
else
{
lean_object* v___x_4048_; lean_object* v___f_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___f_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4048_ = lean_box(v___x_4043_);
lean_inc(v_toBind_4036_);
lean_inc(v_inst_4035_);
v___f_4049_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_4049_, 0, v_toPure_4033_);
lean_closure_set(v___f_4049_, 1, v_levels_x3f_4034_);
lean_closure_set(v___f_4049_, 2, v___x_4048_);
lean_closure_set(v___f_4049_, 3, v_inst_4035_);
lean_closure_set(v___f_4049_, 4, v_toBind_4036_);
lean_closure_set(v___f_4049_, 5, v_params_4037_);
lean_closure_set(v___f_4049_, 6, v_inst_4032_);
lean_closure_set(v___f_4049_, 7, v___f_4038_);
v___x_4050_ = 0;
v___x_4051_ = lean_box(v___x_4050_);
v___f_4052_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4052_, 0, v_cinfo_4031_);
lean_closure_set(v___f_4052_, 1, v_us_4039_);
lean_closure_set(v___f_4052_, 2, v___x_4051_);
v___x_4053_ = lean_apply_2(v_inst_4035_, lean_box(0), v___f_4052_);
v___x_4054_ = lean_apply_4(v_toBind_4036_, lean_box(0), lean_box(0), v___x_4053_, v___f_4049_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4055_, lean_object* v_toPure_4056_, lean_object* v_levels_x3f_4057_, lean_object* v_inst_4058_, lean_object* v_toBind_4059_, lean_object* v_params_4060_, lean_object* v___f_4061_, lean_object* v_cinfo_4062_){
_start:
{
lean_object* v___f_4063_; 
lean_inc(v_toBind_4059_);
lean_inc(v_inst_4058_);
lean_inc(v_levels_x3f_4057_);
lean_inc(v_toPure_4056_);
lean_inc_ref(v_cinfo_4062_);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4063_, 0, v_cinfo_4062_);
lean_closure_set(v___f_4063_, 1, v_inst_4055_);
lean_closure_set(v___f_4063_, 2, v_toPure_4056_);
lean_closure_set(v___f_4063_, 3, v_levels_x3f_4057_);
lean_closure_set(v___f_4063_, 4, v_inst_4058_);
lean_closure_set(v___f_4063_, 5, v_toBind_4059_);
lean_closure_set(v___f_4063_, 6, v_params_4060_);
lean_closure_set(v___f_4063_, 7, v___f_4061_);
if (lean_obj_tag(v_levels_x3f_4057_) == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
lean_dec(v_toPure_4056_);
v___x_4064_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4064_, 0, v_cinfo_4062_);
v___x_4065_ = lean_apply_2(v_inst_4058_, lean_box(0), v___x_4064_);
v___x_4066_ = lean_apply_4(v_toBind_4059_, lean_box(0), lean_box(0), v___x_4065_, v___f_4063_);
return v___x_4066_;
}
else
{
lean_object* v_val_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec_ref(v_cinfo_4062_);
lean_dec(v_inst_4058_);
v_val_4067_ = lean_ctor_get(v_levels_x3f_4057_, 0);
lean_inc(v_val_4067_);
lean_dec_ref(v_levels_x3f_4057_);
v___x_4068_ = lean_apply_2(v_toPure_4056_, lean_box(0), v_val_4067_);
v___x_4069_ = lean_apply_4(v_toBind_4059_, lean_box(0), lean_box(0), v___x_4068_, v___f_4063_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_inst_4072_, lean_object* v_inst_4073_, lean_object* v_defaultFn_4074_, lean_object* v_levels_x3f_4075_, lean_object* v_params_4076_, lean_object* v_fieldVal_x3f_4077_){
_start:
{
lean_object* v_toApplicative_4078_; lean_object* v_toBind_4079_; lean_object* v_toPure_4080_; lean_object* v___x_4081_; lean_object* v___f_4082_; lean_object* v___f_4083_; lean_object* v___x_4084_; 
v_toApplicative_4078_ = lean_ctor_get(v_inst_4070_, 0);
v_toBind_4079_ = lean_ctor_get(v_inst_4070_, 1);
lean_inc_n(v_toBind_4079_, 2);
v_toPure_4080_ = lean_ctor_get(v_toApplicative_4078_, 1);
lean_inc_n(v_toPure_4080_, 2);
lean_inc_ref_n(v_inst_4070_, 2);
v___x_4081_ = l_Lean_getConstInfo___redArg(v_inst_4070_, v_inst_4071_, v_inst_4072_, v_defaultFn_4074_);
lean_inc(v_inst_4073_);
v___f_4082_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4082_, 0, v_inst_4070_);
lean_closure_set(v___f_4082_, 1, v_inst_4073_);
lean_closure_set(v___f_4082_, 2, v_fieldVal_x3f_4077_);
lean_closure_set(v___f_4082_, 3, v_toPure_4080_);
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4083_, 0, v_inst_4070_);
lean_closure_set(v___f_4083_, 1, v_toPure_4080_);
lean_closure_set(v___f_4083_, 2, v_levels_x3f_4075_);
lean_closure_set(v___f_4083_, 3, v_inst_4073_);
lean_closure_set(v___f_4083_, 4, v_toBind_4079_);
lean_closure_set(v___f_4083_, 5, v_params_4076_);
lean_closure_set(v___f_4083_, 6, v___f_4082_);
v___x_4084_ = lean_apply_4(v_toBind_4079_, lean_box(0), lean_box(0), v___x_4081_, v___f_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4085_, lean_object* v_inst_4086_, lean_object* v_inst_4087_, lean_object* v_inst_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_defaultFn_4091_, lean_object* v_levels_x3f_4092_, lean_object* v_params_4093_, lean_object* v_fieldVal_x3f_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4086_, v_inst_4087_, v_inst_4088_, v_inst_4089_, v_defaultFn_4091_, v_levels_x3f_4092_, v_params_4093_, v_fieldVal_x3f_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4096_, lean_object* v_inst_4097_, lean_object* v_inst_4098_, lean_object* v_inst_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_defaultFn_4102_, lean_object* v_levels_x3f_4103_, lean_object* v_params_4104_, lean_object* v_fieldVal_x3f_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4096_, v_inst_4097_, v_inst_4098_, v_inst_4099_, v_inst_4100_, v_inst_4101_, v_defaultFn_4102_, v_levels_x3f_4103_, v_params_4104_, v_fieldVal_x3f_4105_);
lean_dec_ref(v_inst_4101_);
return v_res_4106_;
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
