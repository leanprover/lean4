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
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVarsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_declName_63_);
lean_dec_ref(v___x_62_);
v___x_64_ = lean_st_ref_get(v_a_60_);
v_env_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_env_65_);
lean_dec(v___x_64_);
lean_inc(v_declName_63_);
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
lean_inc_ref(v_env_126_);
lean_dec(v___x_114_);
lean_inc_ref(v_env_126_);
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
v___x_166_ = lean_apply_6(v_k_159_, v_b_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_167_, lean_object* v_b_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_167_, v_b_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
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
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_242_, lean_object* v_b_243_, lean_object* v_c_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_apply_7(v_k_242_, v_b_243_, v_c_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_251_, lean_object* v_b_252_, lean_object* v_c_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_251_, v_b_252_, v_c_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
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
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_fileName_388_; lean_object* v_fileMap_389_; lean_object* v_options_390_; lean_object* v_currRecDepth_391_; lean_object* v_maxRecDepth_392_; lean_object* v_ref_393_; lean_object* v_currNamespace_394_; lean_object* v_openDecls_395_; lean_object* v_initHeartbeats_396_; lean_object* v_maxHeartbeats_397_; lean_object* v_quotContext_398_; lean_object* v_currMacroScope_399_; uint8_t v_diag_400_; lean_object* v_cancelTk_x3f_401_; uint8_t v_suppressElabErrors_402_; lean_object* v_inheritedTraceOptions_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_412_; 
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
v_isSharedCheck_412_ = !lean_is_exclusive(v___y_385_);
if (v_isSharedCheck_412_ == 0)
{
v___x_405_ = v___y_385_;
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_inheritedTraceOptions_403_);
lean_inc(v_cancelTk_x3f_401_);
lean_inc(v_currMacroScope_399_);
lean_inc(v_quotContext_398_);
lean_inc(v_maxHeartbeats_397_);
lean_inc(v_initHeartbeats_396_);
lean_inc(v_openDecls_395_);
lean_inc(v_currNamespace_394_);
lean_inc(v_ref_393_);
lean_inc(v_maxRecDepth_392_);
lean_inc(v_currRecDepth_391_);
lean_inc(v_options_390_);
lean_inc(v_fileMap_389_);
lean_inc(v_fileName_388_);
lean_dec(v___y_385_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_412_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_ref_407_; lean_object* v___x_409_; 
v_ref_407_ = l_Lean_replaceRef(v_ref_381_, v_ref_393_);
lean_dec(v_ref_393_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 5, v_ref_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_fileName_388_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_fileMap_389_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_options_390_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_currRecDepth_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_maxRecDepth_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_ref_407_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_currNamespace_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_openDecls_395_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_initHeartbeats_396_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_maxHeartbeats_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 10, v_quotContext_398_);
lean_ctor_set(v_reuseFailAlloc_411_, 11, v_currMacroScope_399_);
lean_ctor_set(v_reuseFailAlloc_411_, 12, v_cancelTk_x3f_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 13, v_inheritedTraceOptions_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*14, v_diag_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_411_, sizeof(void*)*14 + 1, v_suppressElabErrors_402_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_382_, v___y_383_, v___y_384_, v___x_409_, v___y_386_);
lean_dec_ref(v___x_409_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_413_, lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_413_, v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v_ref_413_);
return v_res_420_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_430_, lean_object* v_projName_431_, lean_object* v_n_432_, lean_object* v_ref_433_, lean_object* v___f_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
if (v___x_430_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_440_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_441_ = l_Lean_MessageData_ofName(v_projName_431_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_MessageData_ofConstName(v_n_432_, v___x_430_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_inc_ref(v___y_437_);
v___x_449_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_433_, v___x_448_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = lean_apply_6(v___f_434_, v_a_450_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec_ref(v___f_434_);
v_a_452_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_449_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_n_432_);
lean_dec(v_projName_431_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_apply_6(v___f_434_, v___x_460_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_462_, lean_object* v_projName_463_, lean_object* v_n_464_, lean_object* v_ref_465_, lean_object* v___f_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_19448__boxed_472_; lean_object* v_res_473_; 
v___x_19448__boxed_472_ = lean_unbox(v___x_462_);
v_res_473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_19448__boxed_472_, v_projName_463_, v_n_464_, v_ref_465_, v___f_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v_ref_465_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_474_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_480_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
lean_ctor_set(v___x_480_, 3, v___x_479_);
lean_ctor_set(v___x_480_, 4, v___x_479_);
lean_ctor_set(v___x_480_, 5, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_481_, uint8_t v_s_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; lean_object* v_env_487_; lean_object* v_nextMacroScope_488_; lean_object* v_ngen_489_; lean_object* v_auxDeclNGen_490_; lean_object* v_traceState_491_; lean_object* v_messages_492_; lean_object* v_infoState_493_; lean_object* v_snapshotTasks_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_523_; 
v___x_486_ = lean_st_ref_take(v___y_484_);
v_env_487_ = lean_ctor_get(v___x_486_, 0);
v_nextMacroScope_488_ = lean_ctor_get(v___x_486_, 1);
v_ngen_489_ = lean_ctor_get(v___x_486_, 2);
v_auxDeclNGen_490_ = lean_ctor_get(v___x_486_, 3);
v_traceState_491_ = lean_ctor_get(v___x_486_, 4);
v_messages_492_ = lean_ctor_get(v___x_486_, 6);
v_infoState_493_ = lean_ctor_get(v___x_486_, 7);
v_snapshotTasks_494_ = lean_ctor_get(v___x_486_, 8);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_486_, 5);
lean_dec(v_unused_524_);
v___x_496_ = v___x_486_;
v_isShared_497_ = v_isSharedCheck_523_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_snapshotTasks_494_);
lean_inc(v_infoState_493_);
lean_inc(v_messages_492_);
lean_inc(v_traceState_491_);
lean_inc(v_auxDeclNGen_490_);
lean_inc(v_ngen_489_);
lean_inc(v_nextMacroScope_488_);
lean_inc(v_env_487_);
lean_dec(v___x_486_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_523_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_498_ = 0;
v___x_499_ = lean_box(0);
v___x_500_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_487_, v_declName_481_, v_s_482_, v___x_498_, v___x_499_);
v___x_501_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 5, v___x_501_);
lean_ctor_set(v___x_496_, 0, v___x_500_);
v___x_503_ = v___x_496_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_nextMacroScope_488_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_ngen_489_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_auxDeclNGen_490_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_traceState_491_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v_messages_492_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v_infoState_493_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_snapshotTasks_494_);
v___x_503_ = v_reuseFailAlloc_522_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_mctx_506_; lean_object* v_zetaDeltaFVarIds_507_; lean_object* v_postponed_508_; lean_object* v_diag_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_520_; 
v___x_504_ = lean_st_ref_set(v___y_484_, v___x_503_);
v___x_505_ = lean_st_ref_take(v___y_483_);
v_mctx_506_ = lean_ctor_get(v___x_505_, 0);
v_zetaDeltaFVarIds_507_ = lean_ctor_get(v___x_505_, 2);
v_postponed_508_ = lean_ctor_get(v___x_505_, 3);
v_diag_509_ = lean_ctor_get(v___x_505_, 4);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v___x_505_, 1);
lean_dec(v_unused_521_);
v___x_511_ = v___x_505_;
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_diag_509_);
lean_inc(v_postponed_508_);
lean_inc(v_zetaDeltaFVarIds_507_);
lean_inc(v_mctx_506_);
lean_dec(v___x_505_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_mctx_506_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_zetaDeltaFVarIds_507_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_postponed_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_diag_509_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_st_ref_set(v___y_483_, v___x_515_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_525_, lean_object* v_s_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
uint8_t v_s_boxed_530_; lean_object* v_res_531_; 
v_s_boxed_530_ = lean_unbox(v_s_526_);
v_res_531_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_525_, v_s_boxed_530_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec(v___y_527_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___x_538_; lean_object* v___x_539_; 
v___x_538_ = 0;
v___x_539_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_532_, v___x_538_, v___y_534_, v___y_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_555_ = l_Lean_stringToMessageData(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_556_, lean_object* v_projName_557_, lean_object* v___x_558_, lean_object* v_a_559_, uint8_t v_instImplicit_560_, lean_object* v___x_561_, lean_object* v_params_562_, lean_object* v_self_563_, lean_object* v_b_564_, uint8_t v___x_565_, lean_object* v_a_566_, lean_object* v___x_567_, lean_object* v_paramInfoOverrides_568_, lean_object* v_n_569_, lean_object* v_ref_570_, lean_object* v___x_571_, uint8_t v_a_572_, lean_object* v_____r_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; uint8_t v___y_642_; uint8_t v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_748_ = l_List_lengthTR___redArg(v_paramInfoOverrides_568_);
v___x_749_ = lean_array_get_size(v_params_562_);
v___x_750_ = lean_nat_dec_le(v___x_748_, v___x_749_);
lean_dec(v___x_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_557_);
v___x_752_ = l_Lean_MessageData_ofName(v_projName_557_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_inc(v_n_569_);
v___x_756_ = l_Lean_MessageData_ofConstName(v_n_569_, v___x_750_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_inc_ref(v___y_576_);
v___x_760_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_570_, v___x_759_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref(v___x_760_);
goto v___jp_709_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___x_571_);
lean_dec(v_n_569_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_self_563_);
lean_dec(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v___x_558_);
lean_dec(v_projName_557_);
lean_dec_ref(v___x_556_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
goto v___jp_709_;
}
v___jp_579_:
{
lean_object* v___x_582_; lean_object* v_env_583_; lean_object* v_nextMacroScope_584_; lean_object* v_ngen_585_; lean_object* v_auxDeclNGen_586_; lean_object* v_traceState_587_; lean_object* v_messages_588_; lean_object* v_infoState_589_; lean_object* v_snapshotTasks_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_622_; 
v___x_582_ = lean_st_ref_take(v___y_580_);
v_env_583_ = lean_ctor_get(v___x_582_, 0);
v_nextMacroScope_584_ = lean_ctor_get(v___x_582_, 1);
v_ngen_585_ = lean_ctor_get(v___x_582_, 2);
v_auxDeclNGen_586_ = lean_ctor_get(v___x_582_, 3);
v_traceState_587_ = lean_ctor_get(v___x_582_, 4);
v_messages_588_ = lean_ctor_get(v___x_582_, 6);
v_infoState_589_ = lean_ctor_get(v___x_582_, 7);
v_snapshotTasks_590_ = lean_ctor_get(v___x_582_, 8);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_582_, 5);
lean_dec(v_unused_623_);
v___x_592_ = v___x_582_;
v_isShared_593_ = v_isSharedCheck_622_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snapshotTasks_590_);
lean_inc(v_infoState_589_);
lean_inc(v_messages_588_);
lean_inc(v_traceState_587_);
lean_inc(v_auxDeclNGen_586_);
lean_inc(v_ngen_585_);
lean_inc(v_nextMacroScope_584_);
lean_inc(v_env_583_);
lean_dec(v___x_582_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_622_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_name_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_name_594_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_name_594_);
lean_dec_ref(v___x_556_);
lean_inc(v_projName_557_);
v___x_595_ = l_Lean_addProjectionFnInfo(v_env_583_, v_projName_557_, v_name_594_, v___x_558_, v_a_559_, v_instImplicit_560_);
v___x_596_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 5, v___x_596_);
lean_ctor_set(v___x_592_, 0, v___x_595_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_nextMacroScope_584_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_ngen_585_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_auxDeclNGen_586_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_traceState_587_);
lean_ctor_set(v_reuseFailAlloc_621_, 5, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_621_, 6, v_messages_588_);
lean_ctor_set(v_reuseFailAlloc_621_, 7, v_infoState_589_);
lean_ctor_set(v_reuseFailAlloc_621_, 8, v_snapshotTasks_590_);
v___x_598_ = v_reuseFailAlloc_621_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_mctx_601_; lean_object* v_zetaDeltaFVarIds_602_; lean_object* v_postponed_603_; lean_object* v_diag_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_619_; 
v___x_599_ = lean_st_ref_set(v___y_580_, v___x_598_);
lean_dec(v___y_580_);
v___x_600_ = lean_st_ref_take(v___y_581_);
v_mctx_601_ = lean_ctor_get(v___x_600_, 0);
v_zetaDeltaFVarIds_602_ = lean_ctor_get(v___x_600_, 2);
v_postponed_603_ = lean_ctor_get(v___x_600_, 3);
v_diag_604_ = lean_ctor_get(v___x_600_, 4);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_600_, 1);
lean_dec(v_unused_620_);
v___x_606_ = v___x_600_;
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_diag_604_);
lean_inc(v_postponed_603_);
lean_inc(v_zetaDeltaFVarIds_602_);
lean_inc(v_mctx_601_);
lean_dec(v___x_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_mctx_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_zetaDeltaFVarIds_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_postponed_603_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_diag_604_);
v___x_610_ = v_reuseFailAlloc_618_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_611_ = lean_st_ref_set(v___y_581_, v___x_610_);
lean_dec(v___y_581_);
v___x_612_ = l_Lean_Expr_const___override(v_projName_557_, v___x_561_);
v___x_613_ = l_Lean_mkAppN(v___x_612_, v_params_562_);
v___x_614_ = l_Lean_Expr_app___override(v___x_613_, v_self_563_);
v___x_615_ = l_Lean_Expr_bindingBody_x21(v_b_564_);
v___x_616_ = lean_expr_instantiate1(v___x_615_, v___x_614_);
lean_dec_ref(v___x_614_);
lean_dec_ref(v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
}
}
}
v___jp_624_:
{
if (lean_obj_tag(v___y_627_) == 0)
{
lean_dec_ref(v___y_627_);
v___y_580_ = v___y_625_;
v___y_581_ = v___y_626_;
goto v___jp_579_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v_self_563_);
lean_dec(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v___x_558_);
lean_dec(v_projName_557_);
lean_dec_ref(v___x_556_);
v_a_628_ = lean_ctor_get(v___y_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___y_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___y_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_636_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_643_ = lean_box(0);
lean_inc(v_projName_557_);
v___x_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_644_, 0, v_projName_557_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_645_, 0, v___y_639_);
lean_ctor_set(v___x_645_, 1, v___y_640_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3, v___x_565_);
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_inc(v___y_637_);
v___x_647_ = l_Lean_addDecl(v___x_646_, v___y_642_, v___y_638_, v___y_637_);
v___y_625_ = v___y_637_;
v___y_626_ = v___y_641_;
v___y_627_ = v___x_647_;
goto v___jp_624_;
}
v___jp_648_:
{
uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v_fileName_657_; lean_object* v_fileMap_658_; lean_object* v_options_659_; lean_object* v_currRecDepth_660_; lean_object* v_maxRecDepth_661_; lean_object* v_ref_662_; lean_object* v_currNamespace_663_; lean_object* v_openDecls_664_; lean_object* v_initHeartbeats_665_; lean_object* v_maxHeartbeats_666_; lean_object* v_quotContext_667_; lean_object* v_currMacroScope_668_; uint8_t v_diag_669_; lean_object* v_cancelTk_x3f_670_; uint8_t v_suppressElabErrors_671_; lean_object* v_inheritedTraceOptions_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_708_; 
v___x_655_ = 0;
lean_inc_ref(v_a_566_);
v___x_656_ = l_Lean_LocalContext_mkForall(v_a_566_, v___x_567_, v___y_650_, v___x_565_, v___x_655_);
lean_dec_ref(v___y_650_);
v_fileName_657_ = lean_ctor_get(v___y_653_, 0);
v_fileMap_658_ = lean_ctor_get(v___y_653_, 1);
v_options_659_ = lean_ctor_get(v___y_653_, 2);
v_currRecDepth_660_ = lean_ctor_get(v___y_653_, 3);
v_maxRecDepth_661_ = lean_ctor_get(v___y_653_, 4);
v_ref_662_ = lean_ctor_get(v___y_653_, 5);
v_currNamespace_663_ = lean_ctor_get(v___y_653_, 6);
v_openDecls_664_ = lean_ctor_get(v___y_653_, 7);
v_initHeartbeats_665_ = lean_ctor_get(v___y_653_, 8);
v_maxHeartbeats_666_ = lean_ctor_get(v___y_653_, 9);
v_quotContext_667_ = lean_ctor_get(v___y_653_, 10);
v_currMacroScope_668_ = lean_ctor_get(v___y_653_, 11);
v_diag_669_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*14);
v_cancelTk_x3f_670_ = lean_ctor_get(v___y_653_, 12);
v_suppressElabErrors_671_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_672_ = lean_ctor_get(v___y_653_, 13);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_653_);
if (v_isSharedCheck_708_ == 0)
{
v___x_674_ = v___y_653_;
v_isShared_675_ = v_isSharedCheck_708_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_inheritedTraceOptions_672_);
lean_inc(v_cancelTk_x3f_670_);
lean_inc(v_currMacroScope_668_);
lean_inc(v_quotContext_667_);
lean_inc(v_maxHeartbeats_666_);
lean_inc(v_initHeartbeats_665_);
lean_inc(v_openDecls_664_);
lean_inc(v_currNamespace_663_);
lean_inc(v_ref_662_);
lean_inc(v_maxRecDepth_661_);
lean_inc(v_currRecDepth_660_);
lean_inc(v_options_659_);
lean_inc(v_fileMap_658_);
lean_inc(v_fileName_657_);
lean_dec(v___y_653_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_708_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_ref_680_; lean_object* v___x_682_; 
v___x_676_ = l_Lean_Expr_inferImplicit(v___x_656_, v___x_558_, v___x_565_);
v___x_677_ = l_Lean_Expr_updateForallBinderInfos(v___x_676_, v_paramInfoOverrides_568_);
lean_inc_ref(v_self_563_);
lean_inc(v_a_559_);
v___x_678_ = l_Lean_Expr_proj___override(v_n_569_, v_a_559_, v_self_563_);
v___x_679_ = l_Lean_LocalContext_mkLambda(v_a_566_, v___x_567_, v___x_678_, v___x_565_, v___x_655_);
lean_dec_ref(v___x_678_);
v_ref_680_ = l_Lean_replaceRef(v_ref_570_, v_ref_662_);
lean_dec(v_ref_662_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 5, v_ref_680_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_fileName_657_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_fileMap_658_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_options_659_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_currRecDepth_660_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_maxRecDepth_661_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_ref_680_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v_currNamespace_663_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_openDecls_664_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_initHeartbeats_665_);
lean_ctor_set(v_reuseFailAlloc_707_, 9, v_maxHeartbeats_666_);
lean_ctor_set(v_reuseFailAlloc_707_, 10, v_quotContext_667_);
lean_ctor_set(v_reuseFailAlloc_707_, 11, v_currMacroScope_668_);
lean_ctor_set(v_reuseFailAlloc_707_, 12, v_cancelTk_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_707_, 13, v_inheritedTraceOptions_672_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*14, v_diag_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*14 + 1, v_suppressElabErrors_671_);
v___x_682_ = v_reuseFailAlloc_707_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
if (v___y_649_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(1);
lean_inc(v_projName_557_);
v___x_684_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_557_, v___x_571_, v___x_677_, v___x_679_, v___x_683_, v___y_654_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_a_685_);
lean_inc(v___y_654_);
lean_inc_ref(v___x_682_);
v___x_687_ = l_Lean_addDecl(v___x_686_, v___x_655_, v___x_682_, v___y_654_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref(v___x_687_);
if (v_instImplicit_560_ == 0)
{
lean_object* v___x_688_; 
lean_inc(v_projName_557_);
v___x_688_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_557_, v___y_651_, v___y_652_, v___x_682_, v___y_654_);
lean_dec_ref(v___x_682_);
lean_dec_ref(v___y_651_);
v___y_625_ = v___y_654_;
v___y_626_ = v___y_652_;
v___y_627_ = v___x_688_;
goto v___jp_624_;
}
else
{
lean_dec_ref(v___x_682_);
lean_dec_ref(v___y_651_);
v___y_580_ = v___y_654_;
v___y_581_ = v___y_652_;
goto v___jp_579_;
}
}
else
{
lean_dec_ref(v___x_682_);
lean_dec_ref(v___y_651_);
v___y_625_ = v___y_654_;
v___y_626_ = v___y_652_;
v___y_627_ = v___x_687_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___x_682_);
lean_dec(v___y_654_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v_self_563_);
lean_dec(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v___x_558_);
lean_dec(v_projName_557_);
lean_dec_ref(v___x_556_);
v_a_689_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_684_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_684_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v___x_697_; lean_object* v_env_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
lean_dec_ref(v___y_651_);
v___x_697_ = lean_st_ref_get(v___y_654_);
v_env_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc_ref(v_env_698_);
lean_dec(v___x_697_);
lean_inc_ref(v___x_677_);
lean_inc(v_projName_557_);
v___x_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_699_, 0, v_projName_557_);
lean_ctor_set(v___x_699_, 1, v___x_571_);
lean_ctor_set(v___x_699_, 2, v___x_677_);
lean_inc_ref(v_env_698_);
v___x_700_ = l_Lean_Environment_hasUnsafe(v_env_698_, v___x_677_);
lean_dec_ref(v___x_677_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_Environment_hasUnsafe(v_env_698_, v___x_679_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = lean_box(0);
lean_inc(v_projName_557_);
v___x_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_703_, 0, v_projName_557_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_704_, 0, v___x_699_);
lean_ctor_set(v___x_704_, 1, v___x_679_);
lean_ctor_set(v___x_704_, 2, v___x_703_);
v___x_705_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_inc(v___y_654_);
v___x_706_ = l_Lean_addDecl(v___x_705_, v___x_655_, v___x_682_, v___y_654_);
v___y_625_ = v___y_654_;
v___y_626_ = v___y_652_;
v___y_627_ = v___x_706_;
goto v___jp_624_;
}
else
{
v___y_637_ = v___y_654_;
v___y_638_ = v___x_682_;
v___y_639_ = v___x_699_;
v___y_640_ = v___x_679_;
v___y_641_ = v___y_652_;
v___y_642_ = v___x_655_;
goto v___jp_636_;
}
}
else
{
lean_dec_ref(v_env_698_);
v___y_637_ = v___y_654_;
v___y_638_ = v___x_682_;
v___y_639_ = v___x_699_;
v___y_640_ = v___x_679_;
v___y_641_ = v___y_652_;
v___y_642_ = v___x_655_;
goto v___jp_636_;
}
}
}
}
}
v___jp_709_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = l_Lean_Expr_bindingDomain_x21(v_b_564_);
v___x_711_ = lean_expr_consume_type_annotations(v___x_710_);
lean_inc(v___y_577_);
lean_inc_ref(v___y_576_);
lean_inc(v___y_575_);
lean_inc_ref(v___y_574_);
lean_inc_ref(v___x_711_);
v___x_712_ = l_Lean_Meta_isProp(v___x_711_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_712_) == 0)
{
if (v_a_572_ == 0)
{
lean_object* v_a_713_; uint8_t v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
v___y_649_ = v___x_714_;
v___y_650_ = v___x_711_;
v___y_651_ = v___y_574_;
v___y_652_ = v___y_575_;
v___y_653_ = v___y_576_;
v___y_654_ = v___y_577_;
goto v___jp_648_;
}
else
{
lean_object* v_a_715_; uint8_t v___x_716_; 
v_a_715_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_712_);
v___x_716_ = lean_unbox(v_a_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_717_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_557_);
v___x_718_ = l_Lean_MessageData_ofName(v_projName_557_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_unbox(v_a_715_);
lean_inc(v_n_569_);
v___x_723_ = l_Lean_MessageData_ofConstName(v_n_569_, v___x_722_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_721_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
lean_inc_ref(v___x_711_);
v___x_727_ = l_Lean_indentExpr(v___x_711_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_inc_ref(v___y_576_);
v___x_729_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_570_, v___x_728_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_729_) == 0)
{
uint8_t v___x_730_; 
lean_dec_ref(v___x_729_);
v___x_730_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
v___y_649_ = v___x_730_;
v___y_650_ = v___x_711_;
v___y_651_ = v___y_574_;
v___y_652_ = v___y_575_;
v___y_653_ = v___y_576_;
v___y_654_ = v___y_577_;
goto v___jp_648_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_715_);
lean_dec_ref(v___x_711_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___x_571_);
lean_dec(v_n_569_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_self_563_);
lean_dec(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v___x_558_);
lean_dec(v_projName_557_);
lean_dec_ref(v___x_556_);
v_a_731_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_729_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
uint8_t v___x_739_; 
v___x_739_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
v___y_649_ = v___x_739_;
v___y_650_ = v___x_711_;
v___y_651_ = v___y_574_;
v___y_652_ = v___y_575_;
v___y_653_ = v___y_576_;
v___y_654_ = v___y_577_;
goto v___jp_648_;
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_711_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___x_571_);
lean_dec(v_n_569_);
lean_dec_ref(v_a_566_);
lean_dec_ref(v_self_563_);
lean_dec(v___x_561_);
lean_dec(v_a_559_);
lean_dec(v___x_558_);
lean_dec(v_projName_557_);
lean_dec_ref(v___x_556_);
v_a_740_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_712_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_712_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_769_ = _args[0];
lean_object* v_projName_770_ = _args[1];
lean_object* v___x_771_ = _args[2];
lean_object* v_a_772_ = _args[3];
lean_object* v_instImplicit_773_ = _args[4];
lean_object* v___x_774_ = _args[5];
lean_object* v_params_775_ = _args[6];
lean_object* v_self_776_ = _args[7];
lean_object* v_b_777_ = _args[8];
lean_object* v___x_778_ = _args[9];
lean_object* v_a_779_ = _args[10];
lean_object* v___x_780_ = _args[11];
lean_object* v_paramInfoOverrides_781_ = _args[12];
lean_object* v_n_782_ = _args[13];
lean_object* v_ref_783_ = _args[14];
lean_object* v___x_784_ = _args[15];
lean_object* v_a_785_ = _args[16];
lean_object* v_____r_786_ = _args[17];
lean_object* v___y_787_ = _args[18];
lean_object* v___y_788_ = _args[19];
lean_object* v___y_789_ = _args[20];
lean_object* v___y_790_ = _args[21];
lean_object* v___y_791_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_792_; uint8_t v___x_19687__boxed_793_; uint8_t v_a_19693__boxed_794_; lean_object* v_res_795_; 
v_instImplicit_boxed_792_ = lean_unbox(v_instImplicit_773_);
v___x_19687__boxed_793_ = lean_unbox(v___x_778_);
v_a_19693__boxed_794_ = lean_unbox(v_a_785_);
v_res_795_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_769_, v_projName_770_, v___x_771_, v_a_772_, v_instImplicit_boxed_792_, v___x_774_, v_params_775_, v_self_776_, v_b_777_, v___x_19687__boxed_793_, v_a_779_, v___x_780_, v_paramInfoOverrides_781_, v_n_782_, v_ref_783_, v___x_784_, v_a_19693__boxed_794_, v_____r_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v_ref_783_);
lean_dec(v_paramInfoOverrides_781_);
lean_dec_ref(v___x_780_);
lean_dec_ref(v_b_777_);
lean_dec_ref(v_params_775_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_796_, uint8_t v_isExporting_797_, lean_object* v___x_798_, lean_object* v___y_799_, lean_object* v___x_800_, lean_object* v_a_x3f_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_env_804_; lean_object* v_nextMacroScope_805_; lean_object* v_ngen_806_; lean_object* v_auxDeclNGen_807_; lean_object* v_traceState_808_; lean_object* v_messages_809_; lean_object* v_infoState_810_; lean_object* v_snapshotTasks_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_836_; 
v___x_803_ = lean_st_ref_take(v___y_796_);
v_env_804_ = lean_ctor_get(v___x_803_, 0);
v_nextMacroScope_805_ = lean_ctor_get(v___x_803_, 1);
v_ngen_806_ = lean_ctor_get(v___x_803_, 2);
v_auxDeclNGen_807_ = lean_ctor_get(v___x_803_, 3);
v_traceState_808_ = lean_ctor_get(v___x_803_, 4);
v_messages_809_ = lean_ctor_get(v___x_803_, 6);
v_infoState_810_ = lean_ctor_get(v___x_803_, 7);
v_snapshotTasks_811_ = lean_ctor_get(v___x_803_, 8);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v___x_803_, 5);
lean_dec(v_unused_837_);
v___x_813_ = v___x_803_;
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snapshotTasks_811_);
lean_inc(v_infoState_810_);
lean_inc(v_messages_809_);
lean_inc(v_traceState_808_);
lean_inc(v_auxDeclNGen_807_);
lean_inc(v_ngen_806_);
lean_inc(v_nextMacroScope_805_);
lean_inc(v_env_804_);
lean_dec(v___x_803_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_836_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_Environment_setExporting(v_env_804_, v_isExporting_797_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 5, v___x_798_);
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_nextMacroScope_805_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ngen_806_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_auxDeclNGen_807_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_traceState_808_);
lean_ctor_set(v_reuseFailAlloc_835_, 5, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_835_, 6, v_messages_809_);
lean_ctor_set(v_reuseFailAlloc_835_, 7, v_infoState_810_);
lean_ctor_set(v_reuseFailAlloc_835_, 8, v_snapshotTasks_811_);
v___x_817_ = v_reuseFailAlloc_835_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_mctx_820_; lean_object* v_zetaDeltaFVarIds_821_; lean_object* v_postponed_822_; lean_object* v_diag_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v___x_818_ = lean_st_ref_set(v___y_796_, v___x_817_);
v___x_819_ = lean_st_ref_take(v___y_799_);
v_mctx_820_ = lean_ctor_get(v___x_819_, 0);
v_zetaDeltaFVarIds_821_ = lean_ctor_get(v___x_819_, 2);
v_postponed_822_ = lean_ctor_get(v___x_819_, 3);
v_diag_823_ = lean_ctor_get(v___x_819_, 4);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_819_, 1);
lean_dec(v_unused_834_);
v___x_825_ = v___x_819_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_diag_823_);
lean_inc(v_postponed_822_);
lean_inc(v_zetaDeltaFVarIds_821_);
lean_inc(v_mctx_820_);
lean_dec(v___x_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_800_);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_mctx_820_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_zetaDeltaFVarIds_821_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_postponed_822_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_diag_823_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_st_ref_set(v___y_799_, v___x_828_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_838_, lean_object* v_isExporting_839_, lean_object* v___x_840_, lean_object* v___y_841_, lean_object* v___x_842_, lean_object* v_a_x3f_843_, lean_object* v___y_844_){
_start:
{
uint8_t v_isExporting_boxed_845_; lean_object* v_res_846_; 
v_isExporting_boxed_845_ = lean_unbox(v_isExporting_839_);
v_res_846_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_838_, v_isExporting_boxed_845_, v___x_840_, v___y_841_, v___x_842_, v_a_x3f_843_);
lean_dec(v_a_x3f_843_);
lean_dec(v___y_841_);
lean_dec(v___y_838_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_847_, uint8_t v_isExporting_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_env_855_; uint8_t v_isExporting_856_; lean_object* v___x_857_; lean_object* v_env_858_; lean_object* v_nextMacroScope_859_; lean_object* v_ngen_860_; lean_object* v_auxDeclNGen_861_; lean_object* v_traceState_862_; lean_object* v_messages_863_; lean_object* v_infoState_864_; lean_object* v_snapshotTasks_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_919_; 
v___x_854_ = lean_st_ref_get(v___y_852_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_854_);
v_isExporting_856_ = lean_ctor_get_uint8(v_env_855_, sizeof(void*)*8);
lean_dec_ref(v_env_855_);
v___x_857_ = lean_st_ref_take(v___y_852_);
v_env_858_ = lean_ctor_get(v___x_857_, 0);
v_nextMacroScope_859_ = lean_ctor_get(v___x_857_, 1);
v_ngen_860_ = lean_ctor_get(v___x_857_, 2);
v_auxDeclNGen_861_ = lean_ctor_get(v___x_857_, 3);
v_traceState_862_ = lean_ctor_get(v___x_857_, 4);
v_messages_863_ = lean_ctor_get(v___x_857_, 6);
v_infoState_864_ = lean_ctor_get(v___x_857_, 7);
v_snapshotTasks_865_ = lean_ctor_get(v___x_857_, 8);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_857_, 5);
lean_dec(v_unused_920_);
v___x_867_ = v___x_857_;
v_isShared_868_ = v_isSharedCheck_919_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snapshotTasks_865_);
lean_inc(v_infoState_864_);
lean_inc(v_messages_863_);
lean_inc(v_traceState_862_);
lean_inc(v_auxDeclNGen_861_);
lean_inc(v_ngen_860_);
lean_inc(v_nextMacroScope_859_);
lean_inc(v_env_858_);
lean_dec(v___x_857_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_919_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = l_Lean_Environment_setExporting(v_env_858_, v_isExporting_848_);
v___x_870_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 5, v___x_870_);
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_nextMacroScope_859_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_ngen_860_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_auxDeclNGen_861_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_traceState_862_);
lean_ctor_set(v_reuseFailAlloc_918_, 5, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_918_, 6, v_messages_863_);
lean_ctor_set(v_reuseFailAlloc_918_, 7, v_infoState_864_);
lean_ctor_set(v_reuseFailAlloc_918_, 8, v_snapshotTasks_865_);
v___x_872_ = v_reuseFailAlloc_918_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_mctx_875_; lean_object* v_zetaDeltaFVarIds_876_; lean_object* v_postponed_877_; lean_object* v_diag_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_916_; 
v___x_873_ = lean_st_ref_set(v___y_852_, v___x_872_);
v___x_874_ = lean_st_ref_take(v___y_850_);
v_mctx_875_ = lean_ctor_get(v___x_874_, 0);
v_zetaDeltaFVarIds_876_ = lean_ctor_get(v___x_874_, 2);
v_postponed_877_ = lean_ctor_get(v___x_874_, 3);
v_diag_878_ = lean_ctor_get(v___x_874_, 4);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_874_, 1);
lean_dec(v_unused_917_);
v___x_880_ = v___x_874_;
v_isShared_881_ = v_isSharedCheck_916_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_diag_878_);
lean_inc(v_postponed_877_);
lean_inc(v_zetaDeltaFVarIds_876_);
lean_inc(v_mctx_875_);
lean_dec(v___x_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_916_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_mctx_875_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_zetaDeltaFVarIds_876_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_postponed_877_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_diag_878_);
v___x_884_ = v_reuseFailAlloc_915_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v_r_886_; 
v___x_885_ = lean_st_ref_set(v___y_850_, v___x_884_);
lean_inc(v___y_852_);
lean_inc(v___y_850_);
v_r_886_ = lean_apply_5(v_x_847_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, lean_box(0));
if (lean_obj_tag(v_r_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_903_; 
v_a_887_ = lean_ctor_get(v_r_886_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_r_886_);
if (v_isSharedCheck_903_ == 0)
{
v___x_889_ = v_r_886_;
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v_r_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
lean_inc(v_a_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_902_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v___x_893_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_852_, v_isExporting_856_, v___x_870_, v___y_850_, v___x_882_, v___x_892_);
lean_dec_ref(v___x_892_);
lean_dec(v___y_850_);
lean_dec(v___y_852_);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_893_, 0);
lean_dec(v_unused_901_);
v___x_895_ = v___x_893_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_dec(v___x_893_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v_a_887_);
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_887_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_904_ = lean_ctor_get(v_r_886_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v_r_886_);
v___x_905_ = lean_box(0);
v___x_906_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_852_, v_isExporting_856_, v___x_870_, v___y_850_, v___x_882_, v___x_905_);
lean_dec(v___y_850_);
lean_dec(v___y_852_);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v___x_906_, 0);
lean_dec(v_unused_914_);
v___x_908_ = v___x_906_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_dec(v___x_906_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 1);
lean_ctor_set(v___x_908_, 0, v_a_904_);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_904_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_921_, lean_object* v_isExporting_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_isExporting_boxed_928_; lean_object* v_res_929_; 
v_isExporting_boxed_928_ = lean_unbox(v_isExporting_922_);
v_res_929_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_921_, v_isExporting_boxed_928_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_930_, uint8_t v_when_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
if (v_when_931_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_apply_5(v_x_930_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, lean_box(0));
return v___x_937_;
}
else
{
uint8_t v___x_938_; lean_object* v___x_939_; 
v___x_938_ = 0;
v___x_939_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_930_, v___x_938_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_940_, lean_object* v_when_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_when_boxed_947_; lean_object* v_res_948_; 
v_when_boxed_947_ = lean_unbox(v_when_941_);
v_res_948_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_940_, v_when_boxed_947_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_949_, lean_object* v_projDecls_950_, lean_object* v___x_951_, lean_object* v___x_952_, uint8_t v_instImplicit_953_, lean_object* v___x_954_, lean_object* v_params_955_, lean_object* v_self_956_, lean_object* v_a_957_, lean_object* v___x_958_, lean_object* v_n_959_, lean_object* v___x_960_, uint8_t v_a_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_lt(v_a_962_, v_upperBound_949_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_a_962_);
lean_dec(v___x_960_);
lean_dec(v_n_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v_a_957_);
lean_dec_ref(v_self_956_);
lean_dec_ref(v_params_955_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_b_963_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v_ref_972_; lean_object* v_projName_973_; lean_object* v_paramInfoOverrides_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___f_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___y_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v___x_971_ = lean_array_fget_borrowed(v_projDecls_950_, v_a_962_);
v_ref_972_ = lean_ctor_get(v___x_971_, 0);
v_projName_973_ = lean_ctor_get(v___x_971_, 1);
v_paramInfoOverrides_974_ = lean_ctor_get(v___x_971_, 2);
v___x_975_ = lean_box(v_instImplicit_953_);
v___x_976_ = lean_box(v___x_969_);
v___x_977_ = lean_box(v_a_961_);
lean_inc(v___x_960_);
lean_inc(v_ref_972_);
lean_inc(v_n_959_);
lean_inc(v_paramInfoOverrides_974_);
lean_inc_ref(v___x_958_);
lean_inc_ref(v_a_957_);
lean_inc_ref(v_b_963_);
lean_inc_ref(v_self_956_);
lean_inc_ref(v_params_955_);
lean_inc(v___x_954_);
lean_inc(v_a_962_);
lean_inc(v___x_952_);
lean_inc(v_projName_973_);
lean_inc_ref(v___x_951_);
v___f_978_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_978_, 0, v___x_951_);
lean_closure_set(v___f_978_, 1, v_projName_973_);
lean_closure_set(v___f_978_, 2, v___x_952_);
lean_closure_set(v___f_978_, 3, v_a_962_);
lean_closure_set(v___f_978_, 4, v___x_975_);
lean_closure_set(v___f_978_, 5, v___x_954_);
lean_closure_set(v___f_978_, 6, v_params_955_);
lean_closure_set(v___f_978_, 7, v_self_956_);
lean_closure_set(v___f_978_, 8, v_b_963_);
lean_closure_set(v___f_978_, 9, v___x_976_);
lean_closure_set(v___f_978_, 10, v_a_957_);
lean_closure_set(v___f_978_, 11, v___x_958_);
lean_closure_set(v___f_978_, 12, v_paramInfoOverrides_974_);
lean_closure_set(v___f_978_, 13, v_n_959_);
lean_closure_set(v___f_978_, 14, v_ref_972_);
lean_closure_set(v___f_978_, 15, v___x_960_);
lean_closure_set(v___f_978_, 16, v___x_977_);
v___x_979_ = l_Lean_Expr_isForall(v_b_963_);
lean_dec_ref(v_b_963_);
v___x_980_ = lean_box(v___x_979_);
lean_inc(v_ref_972_);
lean_inc(v_n_959_);
lean_inc(v_projName_973_);
v___y_981_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_981_, 0, v___x_980_);
lean_closure_set(v___y_981_, 1, v_projName_973_);
lean_closure_set(v___y_981_, 2, v_n_959_);
lean_closure_set(v___y_981_, 3, v_ref_972_);
lean_closure_set(v___y_981_, 4, v___f_978_);
v___x_982_ = l_Lean_isPrivateName(v_projName_973_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
v___x_983_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_981_, v___x_982_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_a_962_, v___x_985_);
lean_dec(v_a_962_);
v_a_962_ = v___x_986_;
v_b_963_ = v_a_984_;
goto _start;
}
else
{
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_a_962_);
lean_dec(v___x_960_);
lean_dec(v_n_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v_a_957_);
lean_dec_ref(v_self_956_);
lean_dec_ref(v_params_955_);
lean_dec(v___x_954_);
lean_dec(v___x_952_);
lean_dec_ref(v___x_951_);
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_988_ = _args[0];
lean_object* v_projDecls_989_ = _args[1];
lean_object* v___x_990_ = _args[2];
lean_object* v___x_991_ = _args[3];
lean_object* v_instImplicit_992_ = _args[4];
lean_object* v___x_993_ = _args[5];
lean_object* v_params_994_ = _args[6];
lean_object* v_self_995_ = _args[7];
lean_object* v_a_996_ = _args[8];
lean_object* v___x_997_ = _args[9];
lean_object* v_n_998_ = _args[10];
lean_object* v___x_999_ = _args[11];
lean_object* v_a_1000_ = _args[12];
lean_object* v_a_1001_ = _args[13];
lean_object* v_b_1002_ = _args[14];
lean_object* v___y_1003_ = _args[15];
lean_object* v___y_1004_ = _args[16];
lean_object* v___y_1005_ = _args[17];
lean_object* v___y_1006_ = _args[18];
lean_object* v___y_1007_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1008_; uint8_t v_a_20292__boxed_1009_; lean_object* v_res_1010_; 
v_instImplicit_boxed_1008_ = lean_unbox(v_instImplicit_992_);
v_a_20292__boxed_1009_ = lean_unbox(v_a_1000_);
v_res_1010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_988_, v_projDecls_989_, v___x_990_, v___x_991_, v_instImplicit_boxed_1008_, v___x_993_, v_params_994_, v_self_995_, v_a_996_, v___x_997_, v_n_998_, v___x_999_, v_a_20292__boxed_1009_, v_a_1001_, v_b_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec_ref(v_projDecls_989_);
lean_dec(v_upperBound_988_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1011_, lean_object* v_as_1012_, size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v___y_1016_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_1015_);
return v___x_1021_;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1022_ = lean_array_uget_borrowed(v_as_1012_, v_i_1014_);
v___x_1023_ = l_Lean_Expr_fvarId_x21(v_a_1022_);
lean_inc_ref(v___y_1016_);
lean_inc(v___x_1023_);
v___x_1024_ = l_Lean_FVarId_getDecl___redArg(v___x_1023_, v___y_1016_, v___y_1017_, v___y_1018_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_a_1027_; uint8_t v___y_1032_; uint8_t v___x_1035_; uint8_t v___x_1036_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref(v___x_1024_);
v___x_1035_ = l_Lean_LocalDecl_binderInfo(v_a_1025_);
v___x_1036_ = l_Lean_BinderInfo_isInstImplicit(v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = l_Lean_LocalDecl_type(v_a_1025_);
lean_dec(v_a_1025_);
v___x_1039_ = lean_is_out_param(v___x_1038_);
if (v___x_1039_ == 0)
{
uint8_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = 0;
v___x_1041_ = l_Lean_LocalContext_setBinderInfo(v_b_1015_, v___x_1023_, v___x_1040_);
v_a_1027_ = v___x_1041_;
goto v___jp_1026_;
}
else
{
goto v___jp_1037_;
}
}
else
{
lean_dec(v_a_1025_);
goto v___jp_1037_;
}
v___jp_1026_:
{
size_t v___x_1028_; size_t v___x_1029_; 
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1014_, v___x_1028_);
v_i_1014_ = v___x_1029_;
v_b_1015_ = v_a_1027_;
goto _start;
}
v___jp_1031_:
{
if (v___y_1032_ == 0)
{
lean_dec(v___x_1023_);
v_a_1027_ = v_b_1015_;
goto v___jp_1026_;
}
else
{
uint8_t v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = 1;
v___x_1034_ = l_Lean_LocalContext_setBinderInfo(v_b_1015_, v___x_1023_, v___x_1033_);
v_a_1027_ = v___x_1034_;
goto v___jp_1026_;
}
}
v___jp_1037_:
{
if (v___x_1036_ == 0)
{
v___y_1032_ = v___x_1036_;
goto v___jp_1031_;
}
else
{
v___y_1032_ = v_instImplicit_1011_;
goto v___jp_1031_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v___x_1023_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_b_1015_);
v_a_1042_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1024_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1024_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1050_, lean_object* v_as_1051_, lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_instImplicit_boxed_1059_; size_t v_sz_boxed_1060_; size_t v_i_boxed_1061_; lean_object* v_res_1062_; 
v_instImplicit_boxed_1059_ = lean_unbox(v_instImplicit_1050_);
v_sz_boxed_1060_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1061_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1059_, v_as_1051_, v_sz_boxed_1060_, v_i_boxed_1061_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1051_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1063_, uint8_t v_instImplicit_1064_, lean_object* v_projDecls_1065_, lean_object* v_toConstantVal_1066_, lean_object* v_numParams_1067_, lean_object* v___x_1068_, lean_object* v_n_1069_, lean_object* v_levelParams_1070_, uint8_t v_a_1071_, lean_object* v_ctorType_1072_, lean_object* v_self_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_lctx_1079_; lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v_lctx_1079_ = lean_ctor_get(v___y_1074_, 2);
lean_inc_ref(v_self_1073_);
lean_inc_ref(v_params_1063_);
v___x_1080_ = lean_array_push(v_params_1063_, v_self_1073_);
v_sz_1081_ = lean_array_size(v_params_1063_);
v___x_1082_ = ((size_t)0ULL);
lean_inc_ref(v___y_1074_);
lean_inc_ref(v_lctx_1079_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1064_, v_params_1063_, v_sz_1081_, v___x_1082_, v_lctx_1079_, v___y_1074_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = lean_array_get_size(v_projDecls_1065_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1085_, v_projDecls_1065_, v_toConstantVal_1066_, v_numParams_1067_, v_instImplicit_1064_, v___x_1068_, v_params_1063_, v_self_1073_, v_a_1084_, v___x_1080_, v_n_1069_, v_levelParams_1070_, v_a_1071_, v___x_1086_, v_ctorType_1072_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1096_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1087_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1087_);
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
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___x_1080_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec_ref(v_self_1073_);
lean_dec_ref(v_ctorType_1072_);
lean_dec(v_levelParams_1070_);
lean_dec(v_n_1069_);
lean_dec(v___x_1068_);
lean_dec(v_numParams_1067_);
lean_dec_ref(v_toConstantVal_1066_);
lean_dec_ref(v_params_1063_);
v_a_1105_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1083_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1083_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1113_, lean_object* v_instImplicit_1114_, lean_object* v_projDecls_1115_, lean_object* v_toConstantVal_1116_, lean_object* v_numParams_1117_, lean_object* v___x_1118_, lean_object* v_n_1119_, lean_object* v_levelParams_1120_, lean_object* v_a_1121_, lean_object* v_ctorType_1122_, lean_object* v_self_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_instImplicit_boxed_1129_; uint8_t v_a_20434__boxed_1130_; lean_object* v_res_1131_; 
v_instImplicit_boxed_1129_ = lean_unbox(v_instImplicit_1114_);
v_a_20434__boxed_1130_ = lean_unbox(v_a_1121_);
v_res_1131_ = l_Lean_Meta_mkProjections___lam__0(v_params_1113_, v_instImplicit_boxed_1129_, v_projDecls_1115_, v_toConstantVal_1116_, v_numParams_1117_, v___x_1118_, v_n_1119_, v_levelParams_1120_, v_a_20434__boxed_1130_, v_ctorType_1122_, v_self_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref(v_projDecls_1115_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1141_, lean_object* v_projDecls_1142_, lean_object* v_toConstantVal_1143_, lean_object* v_numParams_1144_, lean_object* v___x_1145_, lean_object* v_n_1146_, lean_object* v_levelParams_1147_, uint8_t v_a_1148_, lean_object* v_params_1149_, lean_object* v_ctorType_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1167_ = lean_box(v_instImplicit_1141_);
v___x_1168_ = lean_box(v_a_1148_);
lean_inc(v_n_1146_);
lean_inc(v___x_1145_);
lean_inc(v_numParams_1144_);
lean_inc_ref(v_params_1149_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1169_, 0, v_params_1149_);
lean_closure_set(v___f_1169_, 1, v___x_1167_);
lean_closure_set(v___f_1169_, 2, v_projDecls_1142_);
lean_closure_set(v___f_1169_, 3, v_toConstantVal_1143_);
lean_closure_set(v___f_1169_, 4, v_numParams_1144_);
lean_closure_set(v___f_1169_, 5, v___x_1145_);
lean_closure_set(v___f_1169_, 6, v_n_1146_);
lean_closure_set(v___f_1169_, 7, v_levelParams_1147_);
lean_closure_set(v___f_1169_, 8, v___x_1168_);
lean_closure_set(v___f_1169_, 9, v_ctorType_1150_);
v___x_1175_ = lean_array_get_size(v_params_1149_);
v___x_1176_ = lean_nat_dec_eq(v___x_1175_, v_numParams_1144_);
lean_dec(v_numParams_1144_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v___f_1169_);
lean_dec_ref(v_params_1149_);
lean_dec(v___x_1145_);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1178_ = l_Lean_MessageData_ofConstName(v_n_1146_, v___x_1176_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1181_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v___x_1182_;
}
else
{
goto v___jp_1170_;
}
v___jp_1156_:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1165_ = 0;
v___x_1166_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1164_, v___y_1163_, v___y_1162_, v___y_1159_, v___x_1165_, v___y_1160_, v___y_1161_, v___y_1158_, v___y_1157_);
return v___x_1166_;
}
v___jp_1170_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = l_Lean_Expr_const___override(v_n_1146_, v___x_1145_);
v___x_1172_ = l_Lean_mkAppN(v___x_1171_, v_params_1149_);
lean_dec_ref(v_params_1149_);
if (v_instImplicit_1141_ == 0)
{
uint8_t v___x_1173_; 
v___x_1173_ = 0;
v___y_1157_ = v___y_1154_;
v___y_1158_ = v___y_1153_;
v___y_1159_ = v___f_1169_;
v___y_1160_ = v___y_1151_;
v___y_1161_ = v___y_1152_;
v___y_1162_ = v___x_1172_;
v___y_1163_ = v___x_1173_;
goto v___jp_1156_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = 3;
v___y_1157_ = v___y_1154_;
v___y_1158_ = v___y_1153_;
v___y_1159_ = v___f_1169_;
v___y_1160_ = v___y_1151_;
v___y_1161_ = v___y_1152_;
v___y_1162_ = v___x_1172_;
v___y_1163_ = v___x_1174_;
goto v___jp_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1183_, lean_object* v_projDecls_1184_, lean_object* v_toConstantVal_1185_, lean_object* v_numParams_1186_, lean_object* v___x_1187_, lean_object* v_n_1188_, lean_object* v_levelParams_1189_, lean_object* v_a_1190_, lean_object* v_params_1191_, lean_object* v_ctorType_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_instImplicit_boxed_1198_; uint8_t v_a_20538__boxed_1199_; lean_object* v_res_1200_; 
v_instImplicit_boxed_1198_ = lean_unbox(v_instImplicit_1183_);
v_a_20538__boxed_1199_ = lean_unbox(v_a_1190_);
v_res_1200_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1198_, v_projDecls_1184_, v_toConstantVal_1185_, v_numParams_1186_, v___x_1187_, v_n_1188_, v_levelParams_1189_, v_a_20538__boxed_1199_, v_params_1191_, v_ctorType_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
if (lean_obj_tag(v_a_1201_) == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = l_List_reverse___redArg(v_a_1202_);
return v___x_1203_;
}
else
{
lean_object* v_head_1204_; lean_object* v_tail_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1214_; 
v_head_1204_ = lean_ctor_get(v_a_1201_, 0);
v_tail_1205_ = lean_ctor_get(v_a_1201_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1201_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1207_ = v_a_1201_;
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_tail_1205_);
lean_inc(v_head_1204_);
lean_dec(v_a_1201_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = l_Lean_mkLevelParam(v_head_1204_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v_a_1202_);
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_a_1202_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v_a_1201_ = v_tail_1205_;
v_a_1202_ = v___x_1211_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_toApplicative_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1289_; 
v___x_1226_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1227_ = l_ReaderT_instMonad___redArg(v___x_1226_);
v_toApplicative_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1227_, 1);
lean_dec(v_unused_1290_);
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1289_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_toApplicative_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1289_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_toFunctor_1232_; lean_object* v_toSeq_1233_; lean_object* v_toSeqLeft_1234_; lean_object* v_toSeqRight_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1287_; 
v_toFunctor_1232_ = lean_ctor_get(v_toApplicative_1228_, 0);
v_toSeq_1233_ = lean_ctor_get(v_toApplicative_1228_, 2);
v_toSeqLeft_1234_ = lean_ctor_get(v_toApplicative_1228_, 3);
v_toSeqRight_1235_ = lean_ctor_get(v_toApplicative_1228_, 4);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_toApplicative_1228_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_toApplicative_1228_, 1);
lean_dec(v_unused_1288_);
v___x_1237_ = v_toApplicative_1228_;
v_isShared_1238_ = v_isSharedCheck_1287_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_toSeqRight_1235_);
lean_inc(v_toSeqLeft_1234_);
lean_inc(v_toSeq_1233_);
lean_inc(v_toFunctor_1232_);
lean_dec(v_toApplicative_1228_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1287_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1248_; 
v___f_1239_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1240_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1232_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toFunctor_1232_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toFunctor_1232_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___f_1241_);
lean_ctor_set(v___x_1243_, 1, v___f_1242_);
v___f_1244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1244_, 0, v_toSeqRight_1235_);
v___f_1245_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1245_, 0, v_toSeqLeft_1234_);
v___f_1246_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1246_, 0, v_toSeq_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 4, v___f_1244_);
lean_ctor_set(v___x_1237_, 3, v___f_1245_);
lean_ctor_set(v___x_1237_, 2, v___f_1246_);
lean_ctor_set(v___x_1237_, 1, v___f_1239_);
lean_ctor_set(v___x_1237_, 0, v___x_1243_);
v___x_1248_ = v___x_1237_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___f_1239_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___f_1246_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v___f_1245_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v___f_1244_);
v___x_1248_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___f_1240_);
lean_ctor_set(v___x_1230_, 0, v___x_1248_);
v___x_1250_ = v___x_1230_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___f_1240_);
v___x_1250_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v_toApplicative_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1283_; 
v___x_1251_ = l_ReaderT_instMonad___redArg(v___x_1250_);
v_toApplicative_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1251_, 1);
lean_dec(v_unused_1284_);
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_toApplicative_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_toFunctor_1256_; lean_object* v_toSeq_1257_; lean_object* v_toSeqLeft_1258_; lean_object* v_toSeqRight_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1281_; 
v_toFunctor_1256_ = lean_ctor_get(v_toApplicative_1252_, 0);
v_toSeq_1257_ = lean_ctor_get(v_toApplicative_1252_, 2);
v_toSeqLeft_1258_ = lean_ctor_get(v_toApplicative_1252_, 3);
v_toSeqRight_1259_ = lean_ctor_get(v_toApplicative_1252_, 4);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_toApplicative_1252_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_toApplicative_1252_, 1);
lean_dec(v_unused_1282_);
v___x_1261_ = v_toApplicative_1252_;
v_isShared_1262_ = v_isSharedCheck_1281_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_toSeqRight_1259_);
lean_inc(v_toSeqLeft_1258_);
lean_inc(v_toSeq_1257_);
lean_inc(v_toFunctor_1256_);
lean_dec(v_toApplicative_1252_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1281_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___x_1272_; 
v___f_1263_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1264_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1256_);
v___f_1265_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1265_, 0, v_toFunctor_1256_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toFunctor_1256_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___f_1265_);
lean_ctor_set(v___x_1267_, 1, v___f_1266_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeqRight_1259_);
v___f_1269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1269_, 0, v_toSeqLeft_1258_);
v___f_1270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1270_, 0, v_toSeq_1257_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 4, v___f_1268_);
lean_ctor_set(v___x_1261_, 3, v___f_1269_);
lean_ctor_set(v___x_1261_, 2, v___f_1270_);
lean_ctor_set(v___x_1261_, 1, v___f_1263_);
lean_ctor_set(v___x_1261_, 0, v___x_1267_);
v___x_1272_ = v___x_1261_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v___f_1270_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v___f_1269_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v___f_1268_);
v___x_1272_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___f_1264_);
lean_ctor_set(v___x_1254_, 0, v___x_1272_);
v___x_1274_ = v___x_1254_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___f_1264_);
v___x_1274_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_14911__overap_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = l_instInhabitedOfMonad___redArg(v___x_1274_, v___x_1275_);
v___x_14911__overap_1277_ = lean_panic_fn(v___x_1276_, v_msg_1220_);
v___x_1278_ = lean_apply_5(v___x_14911__overap_1277_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
return v___x_1278_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v_res_1297_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1305_ = lean_unsigned_to_nat(11u);
v___x_1306_ = lean_unsigned_to_nat(122u);
v___x_1307_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1308_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1324_; lean_object* v_env_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = lean_st_ref_get(v___y_1314_);
v_env_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = 0;
lean_inc(v_constName_1310_);
v___x_1327_ = l_Lean_Environment_findAsync_x3f(v_env_1325_, v_constName_1310_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 1)
{
lean_object* v_val_1328_; uint8_t v_kind_1329_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1328_);
lean_dec_ref(v___x_1327_);
v_kind_1329_ = lean_ctor_get_uint8(v_val_1328_, sizeof(void*)*3);
if (v_kind_1329_ == 6)
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1328_);
if (lean_obj_tag(v___x_1330_) == 6)
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_constName_1310_);
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 0);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_val_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref(v___x_1330_);
v___x_1339_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
v___x_1340_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1339_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
if (lean_obj_tag(v_a_1341_) == 0)
{
lean_del_object(v___x_1343_);
goto v___jp_1316_;
}
else
{
lean_object* v_val_1345_; lean_object* v___x_1347_; 
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_constName_1310_);
v_val_1345_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_val_1345_);
lean_dec_ref(v_a_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_val_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_val_1345_);
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
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v_constName_1310_);
v_a_1350_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1340_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1340_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
lean_dec(v_val_1328_);
goto v___jp_1316_;
}
}
else
{
lean_dec(v___x_1327_);
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v___x_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1317_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1318_ = 0;
v___x_1319_ = l_Lean_MessageData_ofConstName(v_constName_1310_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1317_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1322_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v_res_1364_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_env_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_st_ref_get(v___y_1372_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
lean_inc(v_constName_1368_);
v___x_1376_ = l_Lean_isInductiveCore_x3f(v_env_1375_, v_constName_1368_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1377_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1378_ = 0;
v___x_1379_ = l_Lean_MessageData_ofConstName(v_constName_1368_, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1377_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1382_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_constName_1368_);
v_val_1384_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1376_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1376_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 0);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_val_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1398_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1401_ = l_Lean_stringToMessageData(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1405_, lean_object* v___x_1406_, uint8_t v_instImplicit_1407_, lean_object* v_projDecls_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
lean_inc(v_n_1405_);
v___x_1414_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1405_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref(v___x_1414_);
v___x_1456_ = l_Lean_InductiveVal_numCtors(v_a_1415_);
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_dec_eq(v___x_1456_, v___x_1457_);
lean_dec(v___x_1456_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v_a_1415_);
lean_dec_ref(v_projDecls_1408_);
lean_dec(v___x_1406_);
v___x_1459_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1460_ = l_Lean_MessageData_ofConstName(v_n_1405_, v___x_1458_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1463_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v___x_1464_;
}
else
{
v___y_1417_ = v___y_1409_;
v___y_1418_ = v___y_1410_;
v___y_1419_ = v___y_1411_;
v___y_1420_ = v___y_1412_;
goto v___jp_1416_;
}
v___jp_1416_:
{
lean_object* v_toConstantVal_1421_; lean_object* v_numParams_1422_; lean_object* v_ctors_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_toConstantVal_1421_ = lean_ctor_get(v_a_1415_, 0);
lean_inc_ref(v_toConstantVal_1421_);
v_numParams_1422_ = lean_ctor_get(v_a_1415_, 1);
lean_inc(v_numParams_1422_);
v_ctors_1423_ = lean_ctor_get(v_a_1415_, 4);
lean_inc(v_ctors_1423_);
lean_dec(v_a_1415_);
v___x_1424_ = l_List_head_x21___redArg(v___x_1406_, v_ctors_1423_);
lean_dec(v_ctors_1423_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1425_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1424_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v_levelParams_1427_; lean_object* v_type_1428_; lean_object* v___x_1429_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v_levelParams_1427_ = lean_ctor_get(v_toConstantVal_1421_, 1);
lean_inc(v_levelParams_1427_);
v_type_1428_ = lean_ctor_get(v_toConstantVal_1421_, 2);
lean_inc_ref(v_type_1428_);
lean_dec_ref(v_toConstantVal_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1429_ = l_Lean_Meta_isPropFormerType(v_type_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_toConstantVal_1430_; lean_object* v_a_1431_; lean_object* v_type_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v_toConstantVal_1430_ = lean_ctor_get(v_a_1426_, 0);
lean_inc_ref(v_toConstantVal_1430_);
lean_dec(v_a_1426_);
v_a_1431_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1429_);
v_type_1432_ = lean_ctor_get(v_toConstantVal_1430_, 2);
lean_inc_ref(v_type_1432_);
v___x_1433_ = lean_box(0);
lean_inc(v_levelParams_1427_);
v___x_1434_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1427_, v___x_1433_);
v___x_1435_ = lean_box(v_instImplicit_1407_);
lean_inc(v_numParams_1422_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1436_, 0, v___x_1435_);
lean_closure_set(v___f_1436_, 1, v_projDecls_1408_);
lean_closure_set(v___f_1436_, 2, v_toConstantVal_1430_);
lean_closure_set(v___f_1436_, 3, v_numParams_1422_);
lean_closure_set(v___f_1436_, 4, v___x_1434_);
lean_closure_set(v___f_1436_, 5, v_n_1405_);
lean_closure_set(v___f_1436_, 6, v_levelParams_1427_);
lean_closure_set(v___f_1436_, 7, v_a_1431_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_numParams_1422_);
v___x_1438_ = 0;
v___x_1439_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1432_, v___x_1437_, v___f_1436_, v___x_1438_, v___x_1438_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1439_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_levelParams_1427_);
lean_dec(v_a_1426_);
lean_dec(v_numParams_1422_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_projDecls_1408_);
lean_dec(v_n_1405_);
v_a_1440_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1429_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1429_);
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
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_numParams_1422_);
lean_dec_ref(v_toConstantVal_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_projDecls_1408_);
lean_dec(v_n_1405_);
v_a_1448_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1425_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1425_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_projDecls_1408_);
lean_dec(v___x_1406_);
lean_dec(v_n_1405_);
v_a_1465_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1414_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1414_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1473_, lean_object* v___x_1474_, lean_object* v_instImplicit_1475_, lean_object* v_projDecls_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v_instImplicit_boxed_1482_; lean_object* v_res_1483_; 
v_instImplicit_boxed_1482_ = lean_unbox(v_instImplicit_1475_);
v_res_1483_ = l_Lean_Meta_mkProjections___lam__2(v_n_1473_, v___x_1474_, v_instImplicit_boxed_1482_, v_projDecls_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v_res_1483_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_unsigned_to_nat(32u);
v___x_1488_ = lean_mk_empty_array_with_capacity(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1490_ = ((size_t)5ULL);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_unsigned_to_nat(32u);
v___x_1493_ = lean_mk_empty_array_with_capacity(v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1495_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
lean_ctor_set(v___x_1495_, 2, v___x_1491_);
lean_ctor_set(v___x_1495_, 3, v___x_1491_);
lean_ctor_set_usize(v___x_1495_, 4, v___x_1490_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1496_ = lean_box(1);
v___x_1497_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1498_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1497_);
lean_ctor_set(v___x_1499_, 2, v___x_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1502_, lean_object* v_projDecls_1503_, uint8_t v_instImplicit_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_box(v_instImplicit_1504_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1512_, 0, v_n_1502_);
lean_closure_set(v___f_1512_, 1, v___x_1510_);
lean_closure_set(v___f_1512_, 2, v___x_1511_);
lean_closure_set(v___f_1512_, 3, v_projDecls_1503_);
v___x_1513_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1514_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1515_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1513_, v___x_1514_, v___f_1512_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1516_, lean_object* v_projDecls_1517_, lean_object* v_instImplicit_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
uint8_t v_instImplicit_boxed_1524_; lean_object* v_res_1525_; 
v_instImplicit_boxed_1524_ = lean_unbox(v_instImplicit_1518_);
v_res_1525_ = l_Lean_Meta_mkProjections(v_n_1516_, v_projDecls_1517_, v_instImplicit_boxed_1524_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1526_, lean_object* v_as_1527_, size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_b_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1526_, v_as_1527_, v_sz_1528_, v_i_1529_, v_b_1530_, v___y_1531_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1537_, lean_object* v_as_1538_, lean_object* v_sz_1539_, lean_object* v_i_1540_, lean_object* v_b_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_instImplicit_boxed_1547_; size_t v_sz_boxed_1548_; size_t v_i_boxed_1549_; lean_object* v_res_1550_; 
v_instImplicit_boxed_1547_ = lean_unbox(v_instImplicit_1537_);
v_sz_boxed_1548_ = lean_unbox_usize(v_sz_1539_);
lean_dec(v_sz_1539_);
v_i_boxed_1549_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1547_, v_as_1538_, v_sz_boxed_1548_, v_i_boxed_1549_, v_b_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_as_1538_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1551_, uint8_t v_s_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1551_, v_s_1552_, v___y_1554_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1559_, lean_object* v_s_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
uint8_t v_s_boxed_1566_; lean_object* v_res_1567_; 
v_s_boxed_1566_ = lean_unbox(v_s_1560_);
v_res_1567_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1559_, v_s_boxed_1566_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1568_, lean_object* v_ref_1569_, lean_object* v_msg_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1569_, v_msg_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_ref_1578_, lean_object* v_msg_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1577_, v_ref_1578_, v_msg_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v_ref_1578_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1586_, lean_object* v_x_1587_, uint8_t v_isExporting_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1587_, v_isExporting_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_x_1596_, lean_object* v_isExporting_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_isExporting_boxed_1603_; lean_object* v_res_1604_; 
v_isExporting_boxed_1603_ = lean_unbox(v_isExporting_1597_);
v_res_1604_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1595_, v_x_1596_, v_isExporting_boxed_1603_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1605_, lean_object* v_x_1606_, uint8_t v_when_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1606_, v_when_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_x_1615_, lean_object* v_when_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_when_boxed_1622_; lean_object* v_res_1623_; 
v_when_boxed_1622_ = lean_unbox(v_when_1616_);
v_res_1623_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1614_, v_x_1615_, v_when_boxed_1622_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1624_, lean_object* v_projDecls_1625_, lean_object* v___x_1626_, lean_object* v___x_1627_, uint8_t v_instImplicit_1628_, lean_object* v___x_1629_, lean_object* v_params_1630_, lean_object* v_self_1631_, lean_object* v_a_1632_, lean_object* v___x_1633_, lean_object* v_n_1634_, lean_object* v___x_1635_, uint8_t v_a_1636_, lean_object* v_inst_1637_, lean_object* v_R_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_, lean_object* v_c_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1624_, v_projDecls_1625_, v___x_1626_, v___x_1627_, v_instImplicit_1628_, v___x_1629_, v_params_1630_, v_self_1631_, v_a_1632_, v___x_1633_, v_n_1634_, v___x_1635_, v_a_1636_, v_a_1639_, v_b_1640_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1648_ = _args[0];
lean_object* v_projDecls_1649_ = _args[1];
lean_object* v___x_1650_ = _args[2];
lean_object* v___x_1651_ = _args[3];
lean_object* v_instImplicit_1652_ = _args[4];
lean_object* v___x_1653_ = _args[5];
lean_object* v_params_1654_ = _args[6];
lean_object* v_self_1655_ = _args[7];
lean_object* v_a_1656_ = _args[8];
lean_object* v___x_1657_ = _args[9];
lean_object* v_n_1658_ = _args[10];
lean_object* v___x_1659_ = _args[11];
lean_object* v_a_1660_ = _args[12];
lean_object* v_inst_1661_ = _args[13];
lean_object* v_R_1662_ = _args[14];
lean_object* v_a_1663_ = _args[15];
lean_object* v_b_1664_ = _args[16];
lean_object* v_c_1665_ = _args[17];
lean_object* v___y_1666_ = _args[18];
lean_object* v___y_1667_ = _args[19];
lean_object* v___y_1668_ = _args[20];
lean_object* v___y_1669_ = _args[21];
lean_object* v___y_1670_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1671_; uint8_t v_a_21303__boxed_1672_; lean_object* v_res_1673_; 
v_instImplicit_boxed_1671_ = lean_unbox(v_instImplicit_1652_);
v_a_21303__boxed_1672_ = lean_unbox(v_a_1660_);
v_res_1673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1648_, v_projDecls_1649_, v___x_1650_, v___x_1651_, v_instImplicit_boxed_1671_, v___x_1653_, v_params_1654_, v_self_1655_, v_a_1656_, v___x_1657_, v_n_1658_, v___x_1659_, v_a_21303__boxed_1672_, v_inst_1661_, v_R_1662_, v_a_1663_, v_b_1664_, v_c_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec_ref(v_projDecls_1649_);
lean_dec(v_upperBound_1648_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1674_, uint8_t v_allowLevelAssignments_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1675_, v_k_1674_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
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
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1681_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1681_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1698_, lean_object* v_allowLevelAssignments_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1705_; lean_object* v_res_1706_; 
v_allowLevelAssignments_boxed_1705_ = lean_unbox(v_allowLevelAssignments_1699_);
v_res_1706_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1698_, v_allowLevelAssignments_boxed_1705_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1707_, lean_object* v_k_1708_, uint8_t v_allowLevelAssignments_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1708_, v_allowLevelAssignments_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_k_1717_, lean_object* v_allowLevelAssignments_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1724_; lean_object* v_res_1725_; 
v_allowLevelAssignments_boxed_1724_ = lean_unbox(v_allowLevelAssignments_1718_);
v_res_1725_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1716_, v_k_1717_, v_allowLevelAssignments_boxed_1724_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1726_, size_t v_sz_1727_, size_t v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_lt(v_i_1728_, v_sz_1727_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_b_1729_);
return v___x_1736_;
}
else
{
lean_object* v_snd_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1792_; 
v_snd_1737_ = lean_ctor_get(v_b_1729_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_b_1729_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_b_1729_, 0);
lean_dec(v_unused_1793_);
v___x_1739_ = v_b_1729_;
v_isShared_1740_ = v_isSharedCheck_1792_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snd_1737_);
lean_dec(v_b_1729_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1792_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_array_1741_; lean_object* v_start_1742_; lean_object* v_stop_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v_array_1741_ = lean_ctor_get(v_snd_1737_, 0);
v_start_1742_ = lean_ctor_get(v_snd_1737_, 1);
v_stop_1743_ = lean_ctor_get(v_snd_1737_, 2);
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_nat_dec_lt(v_start_1742_, v_stop_1743_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1747_; 
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1744_);
v___x_1747_ = v___x_1739_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_snd_1737_);
v___x_1747_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
else
{
lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1788_; 
lean_inc(v_stop_1743_);
lean_inc(v_start_1742_);
lean_inc_ref(v_array_1741_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_snd_1737_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; 
v_unused_1789_ = lean_ctor_get(v_snd_1737_, 2);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_snd_1737_, 1);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_snd_1737_, 0);
lean_dec(v_unused_1791_);
v___x_1751_ = v_snd_1737_;
v_isShared_1752_ = v_isSharedCheck_1788_;
goto v_resetjp_1750_;
}
else
{
lean_dec(v_snd_1737_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1788_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_a_1753_ = lean_array_uget_borrowed(v_as_1726_, v_i_1728_);
v___x_1754_ = lean_array_fget_borrowed(v_array_1741_, v_start_1742_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___x_1754_);
lean_inc(v_a_1753_);
v___x_1755_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1753_, v___x_1754_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1779_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1779_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1779_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_start_1742_, v___x_1760_);
lean_dec(v_start_1742_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 1, v___x_1761_);
v___x_1763_ = v___x_1751_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_array_1741_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_stop_1743_);
v___x_1763_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_unbox(v_a_1756_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1756_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1763_);
lean_ctor_set(v___x_1739_, 0, v___x_1765_);
v___x_1767_ = v___x_1739_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v___x_1763_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1767_);
v___x_1769_ = v___x_1758_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
lean_object* v___x_1773_; 
lean_del_object(v___x_1758_);
lean_dec(v_a_1756_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1763_);
lean_ctor_set(v___x_1739_, 0, v___x_1744_);
v___x_1773_ = v___x_1739_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1763_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
size_t v___x_1774_; size_t v___x_1775_; 
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1728_, v___x_1774_);
v_i_1728_ = v___x_1775_;
v_b_1729_ = v___x_1773_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_del_object(v___x_1751_);
lean_dec(v_stop_1743_);
lean_dec(v_start_1742_);
lean_dec_ref(v_array_1741_);
lean_del_object(v___x_1739_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
v_a_1780_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1755_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1755_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1794_, lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
size_t v_sz_boxed_1803_; size_t v_i_boxed_1804_; lean_object* v_res_1805_; 
v_sz_boxed_1803_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1804_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1794_, v_sz_boxed_1803_, v_i_boxed_1804_, v_b_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v_as_1794_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1806_, lean_object* v_params2_1807_, lean_object* v___x_1808_, lean_object* v_params1_1809_, uint8_t v___x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
if (v___x_1806_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___x_1808_);
lean_dec_ref(v_params2_1807_);
v___x_1816_ = lean_box(v___x_1806_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = l_Array_toSubarray___redArg(v_params2_1807_, v___x_1818_, v___x_1808_);
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1819_);
v_sz_1822_ = lean_array_size(v_params1_1809_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1809_, v_sz_1822_, v___x_1823_, v___x_1821_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1838_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; 
v_fst_1829_ = lean_ctor_get(v_a_1825_, 0);
lean_inc(v_fst_1829_);
lean_dec(v_a_1825_);
if (lean_obj_tag(v_fst_1829_) == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_box(v___x_1810_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1830_);
v___x_1832_ = v___x_1827_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
lean_object* v_val_1834_; lean_object* v___x_1836_; 
v_val_1834_ = lean_ctor_get(v_fst_1829_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v_fst_1829_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v_val_1834_);
v___x_1836_ = v___x_1827_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_val_1834_);
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
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1824_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1824_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1847_, lean_object* v_params2_1848_, lean_object* v___x_1849_, lean_object* v_params1_1850_, lean_object* v___x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
uint8_t v___x_2318__boxed_1857_; uint8_t v___x_2320__boxed_1858_; lean_object* v_res_1859_; 
v___x_2318__boxed_1857_ = lean_unbox(v___x_1847_);
v___x_2320__boxed_1858_ = lean_unbox(v___x_1851_);
v_res_1859_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2318__boxed_1857_, v_params2_1848_, v___x_1849_, v_params1_1850_, v___x_2320__boxed_1858_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec_ref(v_params1_1850_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1860_, lean_object* v_params2_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___y_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1867_ = lean_array_get_size(v_params1_1860_);
v___x_1868_ = lean_array_get_size(v_params2_1861_);
v___x_1869_ = lean_nat_dec_eq(v___x_1867_, v___x_1868_);
v___x_1870_ = 1;
v___x_1871_ = lean_box(v___x_1869_);
v___x_1872_ = lean_box(v___x_1870_);
v___y_1873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1873_, 0, v___x_1871_);
lean_closure_set(v___y_1873_, 1, v_params2_1861_);
lean_closure_set(v___y_1873_, 2, v___x_1868_);
lean_closure_set(v___y_1873_, 3, v_params1_1860_);
lean_closure_set(v___y_1873_, 4, v___x_1872_);
v___x_1874_ = 0;
v___x_1875_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1873_, v___x_1874_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1876_, lean_object* v_params2_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1876_, v_params2_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_env_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_st_ref_get(v___y_1885_);
v_env_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1888_, v_declName_1884_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1891_, v___y_1892_);
lean_dec(v___y_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1895_, v___y_1899_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1909_; lean_object* v_dummy_1910_; 
v___x_1909_ = lean_box(0);
v_dummy_1910_ = l_Lean_Expr_sort___override(v___x_1909_);
return v_dummy_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1911_, lean_object* v_induct_1912_, lean_object* v_params_1913_, lean_object* v_idx_1914_, lean_object* v_e_1915_, lean_object* v_x_x3f_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
if (lean_obj_tag(v_e_1915_) == 11)
{
lean_object* v_typeName_1928_; lean_object* v_idx_1929_; lean_object* v_struct_1930_; uint8_t v___y_1978_; uint8_t v___x_1981_; 
v_typeName_1928_ = lean_ctor_get(v_e_1915_, 0);
v_idx_1929_ = lean_ctor_get(v_e_1915_, 1);
v_struct_1930_ = lean_ctor_get(v_e_1915_, 2);
lean_inc_ref(v_struct_1930_);
v___x_1981_ = lean_nat_dec_eq(v_idx_1929_, v_idx_1914_);
if (v___x_1981_ == 0)
{
v___y_1978_ = v___x_1981_;
goto v___jp_1977_;
}
else
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_name_eq(v_induct_1912_, v_typeName_1928_);
v___y_1978_ = v___x_1982_;
goto v___jp_1977_;
}
v___jp_1931_:
{
lean_object* v___x_1932_; 
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
v___x_1932_ = lean_infer_type(v_e_1915_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
lean_inc(v_a_1920_);
lean_inc_ref(v_a_1919_);
lean_inc(v_a_1918_);
lean_inc_ref(v_a_1917_);
v___x_1934_ = lean_whnf(v_a_1933_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v_dummy_1936_; lean_object* v_nargs_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
v_dummy_1936_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1937_ = l_Lean_Expr_getAppNumArgs(v_a_1935_);
lean_inc(v_nargs_1937_);
v___x_1938_ = lean_mk_array(v_nargs_1937_, v_dummy_1936_);
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_sub(v_nargs_1937_, v___x_1939_);
lean_dec(v_nargs_1937_);
v___x_1941_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1935_, v___x_1938_, v___x_1940_);
v___x_1942_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1913_, v___x_1941_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1952_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1952_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1952_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1947_ == 0)
{
lean_del_object(v___x_1945_);
lean_dec_ref(v_struct_1930_);
goto v___jp_1922_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_struct_1930_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1948_);
v___x_1950_ = v___x_1945_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
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
lean_dec_ref(v_struct_1930_);
v_a_1953_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1942_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1942_);
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
lean_dec_ref(v_struct_1930_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_params_1913_);
v_a_1961_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1934_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1934_);
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
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_struct_1930_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_params_1913_);
v_a_1969_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1932_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1932_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
v___jp_1977_:
{
if (v___y_1978_ == 0)
{
lean_dec_ref(v_struct_1930_);
lean_dec_ref(v_e_1915_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_params_1913_);
goto v___jp_1922_;
}
else
{
if (lean_obj_tag(v_x_x3f_1916_) == 0)
{
goto v___jp_1931_;
}
else
{
lean_object* v_val_1979_; uint8_t v___x_1980_; 
v_val_1979_ = lean_ctor_get(v_x_x3f_1916_, 0);
v___x_1980_ = lean_expr_eqv(v_val_1979_, v_struct_1930_);
if (v___x_1980_ == 0)
{
lean_dec_ref(v_struct_1930_);
lean_dec_ref(v_e_1915_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_params_1913_);
goto v___jp_1922_;
}
else
{
goto v___jp_1931_;
}
}
}
}
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Expr_getAppFn(v_e_1915_);
if (lean_obj_tag(v___x_1983_) == 4)
{
lean_object* v_declName_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2035_; 
v_declName_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_declName_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1984_, v_a_1920_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2035_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2035_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___y_1991_; lean_object* v___y_1992_; 
if (lean_obj_tag(v_a_1986_) == 1)
{
lean_object* v_val_2020_; lean_object* v_ctorName_2021_; lean_object* v_numParams_2022_; lean_object* v_i_2023_; uint8_t v___y_2025_; uint8_t v___x_2033_; 
v_val_2020_ = lean_ctor_get(v_a_1986_, 0);
lean_inc(v_val_2020_);
lean_dec_ref(v_a_1986_);
v_ctorName_2021_ = lean_ctor_get(v_val_2020_, 0);
lean_inc(v_ctorName_2021_);
v_numParams_2022_ = lean_ctor_get(v_val_2020_, 1);
lean_inc(v_numParams_2022_);
v_i_2023_ = lean_ctor_get(v_val_2020_, 2);
lean_inc(v_i_2023_);
lean_dec(v_val_2020_);
v___x_2033_ = lean_name_eq(v_ctorName_2021_, v_ctor_1911_);
lean_dec(v_ctorName_2021_);
if (v___x_2033_ == 0)
{
lean_dec(v_i_2023_);
v___y_2025_ = v___x_2033_;
goto v___jp_2024_;
}
else
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_nat_dec_eq(v_i_2023_, v_idx_1914_);
lean_dec(v_i_2023_);
v___y_2025_ = v___x_2034_;
goto v___jp_2024_;
}
v___jp_2024_:
{
if (v___y_2025_ == 0)
{
lean_dec(v_numParams_2022_);
lean_del_object(v___x_1988_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_e_1915_);
lean_dec_ref(v_params_1913_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2026_ = l_Lean_Expr_getAppNumArgs(v_e_1915_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_add(v_numParams_2022_, v___x_2027_);
lean_dec(v_numParams_2022_);
v___x_2029_ = lean_nat_dec_eq(v___x_2026_, v___x_2028_);
lean_dec(v___x_2028_);
lean_dec(v___x_2026_);
if (v___x_2029_ == 0)
{
lean_del_object(v___x_1988_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_e_1915_);
lean_dec_ref(v_params_1913_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Expr_appArg_x21(v_e_1915_);
if (lean_obj_tag(v_x_x3f_1916_) == 0)
{
v___y_1991_ = v___x_2030_;
v___y_1992_ = v___x_2027_;
goto v___jp_1990_;
}
else
{
lean_object* v_val_2031_; uint8_t v___x_2032_; 
v_val_2031_ = lean_ctor_get(v_x_x3f_1916_, 0);
v___x_2032_ = lean_expr_eqv(v_val_2031_, v___x_2030_);
if (v___x_2032_ == 0)
{
lean_dec_ref(v___x_2030_);
lean_del_object(v___x_1988_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_e_1915_);
lean_dec_ref(v_params_1913_);
goto v___jp_1925_;
}
else
{
v___y_1991_ = v___x_2030_;
v___y_1992_ = v___x_2027_;
goto v___jp_1990_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1988_);
lean_dec(v_a_1986_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_e_1915_);
lean_dec_ref(v_params_1913_);
goto v___jp_1925_;
}
v___jp_1990_:
{
lean_object* v___x_1993_; lean_object* v_dummy_1994_; lean_object* v_nargs_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1993_ = l_Lean_Expr_appFn_x21(v_e_1915_);
lean_dec_ref(v_e_1915_);
v_dummy_1994_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1995_ = l_Lean_Expr_getAppNumArgs(v___x_1993_);
lean_inc(v_nargs_1995_);
v___x_1996_ = lean_mk_array(v_nargs_1995_, v_dummy_1994_);
v___x_1997_ = lean_nat_sub(v_nargs_1995_, v___y_1992_);
lean_dec(v_nargs_1995_);
v___x_1998_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1993_, v___x_1996_, v___x_1997_);
v___x_1999_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1913_, v___x_1998_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2011_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2011_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2011_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_unbox(v_a_2000_);
lean_dec(v_a_2000_);
if (v___x_2004_ == 0)
{
lean_del_object(v___x_2002_);
lean_dec_ref(v___y_1991_);
lean_del_object(v___x_1988_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_2006_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 0, v___y_1991_);
v___x_2006_ = v___x_1988_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___y_1991_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2006_);
v___x_2008_ = v___x_2002_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v___y_1991_);
lean_del_object(v___x_1988_);
v_a_2012_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1999_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1999_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1983_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec_ref(v_e_1915_);
lean_dec_ref(v_params_1913_);
goto v___jp_1925_;
}
}
v___jp_1922_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
v___jp_1925_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2036_, lean_object* v_induct_2037_, lean_object* v_params_2038_, lean_object* v_idx_2039_, lean_object* v_e_2040_, lean_object* v_x_x3f_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2036_, v_induct_2037_, v_params_2038_, v_idx_2039_, v_e_2040_, v_x_x3f_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_x_x3f_2041_);
lean_dec(v_idx_2039_);
lean_dec(v_induct_2037_);
lean_dec(v_ctor_2036_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v_env_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2054_ = lean_st_ref_get(v___y_2052_);
v_env_2058_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref(v_env_2058_);
lean_dec(v___x_2054_);
v___x_2059_ = 0;
v___x_2060_ = l_Lean_Environment_findAsync_x3f(v_env_2058_, v_constName_2048_, v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 1)
{
lean_object* v_val_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2080_; 
v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2080_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_val_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2080_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
uint8_t v_kind_2065_; 
v_kind_2065_ = lean_ctor_get_uint8(v_val_2061_, sizeof(void*)*3);
if (v_kind_2065_ == 6)
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2061_);
if (lean_obj_tag(v___x_2066_) == 6)
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
v_val_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_val_2067_);
v___x_2072_ = v___x_2063_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_val_2067_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec_ref(v___x_2066_);
lean_del_object(v___x_2063_);
v___x_2078_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2079_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2078_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2079_;
}
}
else
{
lean_del_object(v___x_2063_);
lean_dec(v_val_2061_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
goto v___jp_2055_;
}
}
}
else
{
lean_dec(v___x_2060_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
goto v___jp_2055_;
}
v___jp_2055_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v_declName_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_a_2102_, lean_object* v_val_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_nat_dec_lt(v_a_2104_, v_upperBound_2096_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2101_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_b_2105_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v_b_2105_);
v___x_2113_ = l_Lean_instInhabitedExpr;
v___x_2114_ = lean_nat_add(v___x_2097_, v_a_2104_);
v___x_2115_ = lean_array_get_borrowed(v___x_2113_, v___x_2098_, v___x_2114_);
lean_dec(v___x_2114_);
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___x_2115_);
lean_inc_ref(v___x_2101_);
v___x_2116_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2099_, v___x_2100_, v___x_2101_, v_a_2104_, v___x_2115_, v_a_2102_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2135_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2135_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2135_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (lean_obj_tag(v_a_2117_) == 1)
{
lean_object* v_val_2121_; uint8_t v___x_2122_; 
v_val_2121_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_val_2121_);
lean_dec_ref(v_a_2117_);
v___x_2122_ = lean_expr_eqv(v_val_2121_, v_val_2103_);
lean_dec(v_val_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2101_);
v___x_2123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2123_);
v___x_2125_ = v___x_2119_;
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
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_del_object(v___x_2119_);
v___x_2127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2128_ = lean_unsigned_to_nat(1u);
v___x_2129_ = lean_nat_add(v_a_2104_, v___x_2128_);
lean_dec(v_a_2104_);
v_a_2104_ = v___x_2129_;
v_b_2105_ = v___x_2127_;
goto _start;
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec(v_a_2117_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2101_);
v___x_2131_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2131_);
v___x_2133_ = v___x_2119_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
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
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2101_);
v_a_2136_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2116_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2116_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_declName_2147_, lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v_a_2150_, lean_object* v_val_2151_, lean_object* v_a_2152_, lean_object* v_b_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2144_, v___x_2145_, v___x_2146_, v_declName_2147_, v___x_2148_, v___x_2149_, v_a_2150_, v_val_2151_, v_a_2152_, v_b_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec_ref(v_val_2151_);
lean_dec(v_a_2150_);
lean_dec(v___x_2148_);
lean_dec(v_declName_2147_);
lean_dec_ref(v___x_2146_);
lean_dec(v___x_2145_);
lean_dec(v_upperBound_2144_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2160_, lean_object* v_p_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Expr_getAppFn(v_e_2160_);
if (lean_obj_tag(v___x_2167_) == 4)
{
lean_object* v_declName_2168_; lean_object* v___x_2169_; 
v_declName_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_declName_2168_);
lean_dec_ref(v___x_2167_);
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc(v_declName_2168_);
v___x_2169_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2168_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2242_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2242_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2242_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
if (lean_obj_tag(v_a_2170_) == 1)
{
lean_object* v_val_2174_; lean_object* v_induct_2175_; lean_object* v_numParams_2176_; lean_object* v_numFields_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_val_2174_ = lean_ctor_get(v_a_2170_, 0);
lean_inc(v_val_2174_);
lean_dec_ref(v_a_2170_);
v_induct_2175_ = lean_ctor_get(v_val_2174_, 1);
lean_inc(v_induct_2175_);
v_numParams_2176_ = lean_ctor_get(v_val_2174_, 3);
lean_inc(v_numParams_2176_);
v_numFields_2177_ = lean_ctor_get(v_val_2174_, 4);
lean_inc(v_numFields_2177_);
lean_dec(v_val_2174_);
lean_inc(v_induct_2175_);
v___x_2178_ = lean_apply_1(v_p_2161_, v_induct_2175_);
v___x_2179_ = lean_unbox(v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec(v_numFields_2177_);
lean_dec(v_numParams_2176_);
lean_dec(v_induct_2175_);
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_e_2160_);
v___x_2180_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2180_);
v___x_2182_ = v___x_2172_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v___x_2184_; uint8_t v___y_2186_; uint8_t v___x_2234_; 
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2234_ = lean_nat_dec_lt(v___x_2184_, v_numFields_2177_);
if (v___x_2234_ == 0)
{
v___y_2186_ = v___x_2234_;
goto v___jp_2185_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2235_ = l_Lean_Expr_getAppNumArgs(v_e_2160_);
v___x_2236_ = lean_nat_add(v_numParams_2176_, v_numFields_2177_);
v___x_2237_ = lean_nat_dec_eq(v___x_2235_, v___x_2236_);
lean_dec(v___x_2236_);
lean_dec(v___x_2235_);
v___y_2186_ = v___x_2237_;
goto v___jp_2185_;
}
v___jp_2185_:
{
if (v___y_2186_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
lean_dec(v_numFields_2177_);
lean_dec(v_numParams_2176_);
lean_dec(v_induct_2175_);
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_e_2160_);
v___x_2187_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2187_);
v___x_2189_ = v___x_2172_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
else
{
lean_object* v_dummy_2191_; lean_object* v_nargs_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_del_object(v___x_2172_);
v_dummy_2191_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2192_ = l_Lean_Expr_getAppNumArgs(v_e_2160_);
lean_inc(v_nargs_2192_);
v___x_2193_ = lean_mk_array(v_nargs_2192_, v_dummy_2191_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v_nargs_2192_, v___x_2194_);
lean_dec(v_nargs_2192_);
v___x_2196_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2160_, v___x_2193_, v___x_2195_);
lean_inc(v_numParams_2176_);
v___x_2197_ = l_Array_extract___redArg(v___x_2196_, v___x_2184_, v_numParams_2176_);
v___x_2198_ = l_Lean_instInhabitedExpr;
v___x_2199_ = lean_array_get(v___x_2198_, v___x_2196_, v_numParams_2176_);
v___x_2200_ = lean_box(0);
lean_inc(v_a_2165_);
lean_inc_ref(v_a_2164_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc_ref(v___x_2197_);
v___x_2201_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2168_, v_induct_2175_, v___x_2197_, v___x_2184_, v___x_2199_, v___x_2200_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2233_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2233_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2233_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
if (lean_obj_tag(v_a_2202_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_del_object(v___x_2204_);
v_val_2206_ = lean_ctor_get(v_a_2202_, 0);
v___x_2207_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2177_, v_numParams_2176_, v___x_2196_, v_declName_2168_, v_induct_2175_, v___x_2197_, v_a_2202_, v_val_2206_, v___x_2194_, v___x_2207_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_induct_2175_);
lean_dec(v_declName_2168_);
lean_dec_ref(v___x_2196_);
lean_dec(v_numParams_2176_);
lean_dec(v_numFields_2177_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2221_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2221_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2221_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_fst_2213_; 
v_fst_2213_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_fst_2213_);
lean_dec(v_a_2209_);
if (lean_obj_tag(v_fst_2213_) == 0)
{
lean_object* v___x_2215_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_a_2202_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2202_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
else
{
lean_object* v_val_2217_; lean_object* v___x_2219_; 
lean_dec_ref(v_a_2202_);
v_val_2217_ = lean_ctor_get(v_fst_2213_, 0);
lean_inc(v_val_2217_);
lean_dec_ref(v_fst_2213_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_val_2217_);
v___x_2219_ = v___x_2211_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_val_2217_);
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
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v_a_2202_);
v_a_2222_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2208_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2208_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_a_2202_);
lean_dec_ref(v___x_2197_);
lean_dec_ref(v___x_2196_);
lean_dec(v_numFields_2177_);
lean_dec(v_numParams_2176_);
lean_dec(v_induct_2175_);
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2200_);
v___x_2231_ = v___x_2204_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2200_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_dec_ref(v___x_2197_);
lean_dec_ref(v___x_2196_);
lean_dec(v_numFields_2177_);
lean_dec(v_numParams_2176_);
lean_dec(v_induct_2175_);
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec(v_a_2170_);
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_p_2161_);
lean_dec_ref(v_e_2160_);
v___x_2238_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2238_);
v___x_2240_ = v___x_2172_;
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
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_declName_2168_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_p_2161_);
lean_dec_ref(v_e_2160_);
v_a_2243_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2169_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2169_);
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
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v___x_2167_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec_ref(v_p_2161_);
lean_dec_ref(v_e_2160_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2253_, lean_object* v_p_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Meta_etaStruct_x3f(v_e_2253_, v_p_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2261_, lean_object* v___x_2262_, lean_object* v___x_2263_, lean_object* v_declName_2264_, lean_object* v___x_2265_, lean_object* v___x_2266_, lean_object* v_a_2267_, lean_object* v_val_2268_, lean_object* v_inst_2269_, lean_object* v_R_2270_, lean_object* v_a_2271_, lean_object* v_b_2272_, lean_object* v_c_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2261_, v___x_2262_, v___x_2263_, v_declName_2264_, v___x_2265_, v___x_2266_, v_a_2267_, v_val_2268_, v_a_2271_, v_b_2272_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2280_ = _args[0];
lean_object* v___x_2281_ = _args[1];
lean_object* v___x_2282_ = _args[2];
lean_object* v_declName_2283_ = _args[3];
lean_object* v___x_2284_ = _args[4];
lean_object* v___x_2285_ = _args[5];
lean_object* v_a_2286_ = _args[6];
lean_object* v_val_2287_ = _args[7];
lean_object* v_inst_2288_ = _args[8];
lean_object* v_R_2289_ = _args[9];
lean_object* v_a_2290_ = _args[10];
lean_object* v_b_2291_ = _args[11];
lean_object* v_c_2292_ = _args[12];
lean_object* v___y_2293_ = _args[13];
lean_object* v___y_2294_ = _args[14];
lean_object* v___y_2295_ = _args[15];
lean_object* v___y_2296_ = _args[16];
lean_object* v___y_2297_ = _args[17];
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2280_, v___x_2281_, v___x_2282_, v_declName_2283_, v___x_2284_, v___x_2285_, v_a_2286_, v_val_2287_, v_inst_2288_, v_R_2289_, v_a_2290_, v_b_2291_, v_c_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec_ref(v_val_2287_);
lean_dec(v_a_2286_);
lean_dec(v___x_2284_);
lean_dec(v_declName_2283_);
lean_dec_ref(v___x_2282_);
lean_dec(v___x_2281_);
lean_dec(v_upperBound_2280_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = l_Lean_Expr_hasMVar(v_e_2299_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_e_2299_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v_mctx_2305_; lean_object* v___x_2306_; lean_object* v_fst_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; lean_object* v_cache_2310_; lean_object* v_zetaDeltaFVarIds_2311_; lean_object* v_postponed_2312_; lean_object* v_diag_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v___x_2304_ = lean_st_ref_get(v___y_2300_);
v_mctx_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc_ref(v_mctx_2305_);
lean_dec(v___x_2304_);
v___x_2306_ = l_Lean_instantiateMVarsCore(v_mctx_2305_, v_e_2299_);
v_fst_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_fst_2307_);
v_snd_2308_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_snd_2308_);
lean_dec_ref(v___x_2306_);
v___x_2309_ = lean_st_ref_take(v___y_2300_);
v_cache_2310_ = lean_ctor_get(v___x_2309_, 1);
v_zetaDeltaFVarIds_2311_ = lean_ctor_get(v___x_2309_, 2);
v_postponed_2312_ = lean_ctor_get(v___x_2309_, 3);
v_diag_2313_ = lean_ctor_get(v___x_2309_, 4);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2309_, 0);
lean_dec(v_unused_2323_);
v___x_2315_ = v___x_2309_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_diag_2313_);
lean_inc(v_postponed_2312_);
lean_inc(v_zetaDeltaFVarIds_2311_);
lean_inc(v_cache_2310_);
lean_dec(v___x_2309_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_snd_2308_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_snd_2308_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_zetaDeltaFVarIds_2311_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_postponed_2312_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_diag_2313_);
v___x_2318_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_st_ref_set(v___y_2300_, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_fst_2307_);
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2324_, v___y_2325_);
lean_dec(v___y_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2328_, v___y_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v_x_2352_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2359_, lean_object* v_e_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_etaStruct_x3f(v_e_2360_, v_p_2359_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2386_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2386_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2386_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
if (lean_obj_tag(v_a_2367_) == 1)
{
lean_object* v_val_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2381_; 
v_val_2371_ = lean_ctor_get(v_a_2367_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_a_2367_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2373_ = v_a_2367_;
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_val_2371_);
lean_dec(v_a_2367_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 0);
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_val_2371_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2376_);
v___x_2378_ = v___x_2369_;
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
lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec(v_a_2367_);
v___x_2382_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2382_);
v___x_2384_ = v___x_2369_;
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
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2366_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2366_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2395_, lean_object* v_e_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2395_, v_e_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_apply_1(v_x_2404_, lean_box(0));
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2412_, v_x_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2420_, lean_object* v_b_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_dec(v_b_2421_);
lean_dec_ref(v_a_2420_);
return v_x_2422_;
}
else
{
lean_object* v_key_2423_; lean_object* v_value_2424_; lean_object* v_tail_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2437_; 
v_key_2423_ = lean_ctor_get(v_x_2422_, 0);
v_value_2424_ = lean_ctor_get(v_x_2422_, 1);
v_tail_2425_ = lean_ctor_get(v_x_2422_, 2);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_x_2422_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2427_ = v_x_2422_;
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_tail_2425_);
lean_inc(v_value_2424_);
lean_inc(v_key_2423_);
lean_dec(v_x_2422_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_ExprStructEq_beq(v_key_2423_, v_a_2420_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2420_, v_b_2421_, v_tail_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 2, v___x_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_key_2423_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_value_2424_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v___x_2435_; 
lean_dec(v_value_2424_);
lean_dec(v_key_2423_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v_b_2421_);
lean_ctor_set(v___x_2427_, 0, v_a_2420_);
v___x_2435_ = v___x_2427_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2420_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_b_2421_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_tail_2425_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
if (lean_obj_tag(v_x_2439_) == 0)
{
return v_x_2438_;
}
else
{
lean_object* v_key_2440_; lean_object* v_value_2441_; lean_object* v_tail_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2465_; 
v_key_2440_ = lean_ctor_get(v_x_2439_, 0);
v_value_2441_ = lean_ctor_get(v_x_2439_, 1);
v_tail_2442_ = lean_ctor_get(v_x_2439_, 2);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_x_2439_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2444_ = v_x_2439_;
v_isShared_2445_ = v_isSharedCheck_2465_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_tail_2442_);
lean_inc(v_value_2441_);
lean_inc(v_key_2440_);
lean_dec(v_x_2439_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2465_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; uint64_t v___x_2447_; uint64_t v___x_2448_; uint64_t v___x_2449_; uint64_t v_fold_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2446_ = lean_array_get_size(v_x_2438_);
v___x_2447_ = l_Lean_ExprStructEq_hash(v_key_2440_);
v___x_2448_ = 32ULL;
v___x_2449_ = lean_uint64_shift_right(v___x_2447_, v___x_2448_);
v_fold_2450_ = lean_uint64_xor(v___x_2447_, v___x_2449_);
v___x_2451_ = 16ULL;
v___x_2452_ = lean_uint64_shift_right(v_fold_2450_, v___x_2451_);
v___x_2453_ = lean_uint64_xor(v_fold_2450_, v___x_2452_);
v___x_2454_ = lean_uint64_to_usize(v___x_2453_);
v___x_2455_ = lean_usize_of_nat(v___x_2446_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_sub(v___x_2455_, v___x_2456_);
v___x_2458_ = lean_usize_land(v___x_2454_, v___x_2457_);
v___x_2459_ = lean_array_uget_borrowed(v_x_2438_, v___x_2458_);
lean_inc(v___x_2459_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 2, v___x_2459_);
v___x_2461_ = v___x_2444_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_key_2440_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_value_2441_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_array_uset(v_x_2438_, v___x_2458_, v___x_2461_);
v_x_2438_ = v___x_2462_;
v_x_2439_ = v_tail_2442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2466_, lean_object* v_source_2467_, lean_object* v_target_2468_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = lean_array_get_size(v_source_2467_);
v___x_2470_ = lean_nat_dec_lt(v_i_2466_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v_source_2467_);
lean_dec(v_i_2466_);
return v_target_2468_;
}
else
{
lean_object* v_es_2471_; lean_object* v___x_2472_; lean_object* v_source_2473_; lean_object* v_target_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_es_2471_ = lean_array_fget(v_source_2467_, v_i_2466_);
v___x_2472_ = lean_box(0);
v_source_2473_ = lean_array_fset(v_source_2467_, v_i_2466_, v___x_2472_);
v_target_2474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2468_, v_es_2471_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_i_2466_, v___x_2475_);
lean_dec(v_i_2466_);
v_i_2466_ = v___x_2476_;
v_source_2467_ = v_source_2473_;
v_target_2468_ = v_target_2474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2478_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_nbuckets_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2479_ = lean_array_get_size(v_data_2478_);
v___x_2480_ = lean_unsigned_to_nat(2u);
v_nbuckets_2481_ = lean_nat_mul(v___x_2479_, v___x_2480_);
v___x_2482_ = lean_unsigned_to_nat(0u);
v___x_2483_ = lean_box(0);
v___x_2484_ = lean_mk_array(v_nbuckets_2481_, v___x_2483_);
v___x_2485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2482_, v_data_2478_, v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2486_, lean_object* v_x_2487_){
_start:
{
if (lean_obj_tag(v_x_2487_) == 0)
{
uint8_t v___x_2488_; 
v___x_2488_ = 0;
return v___x_2488_;
}
else
{
lean_object* v_key_2489_; lean_object* v_tail_2490_; uint8_t v___x_2491_; 
v_key_2489_ = lean_ctor_get(v_x_2487_, 0);
v_tail_2490_ = lean_ctor_get(v_x_2487_, 2);
v___x_2491_ = l_Lean_ExprStructEq_beq(v_key_2489_, v_a_2486_);
if (v___x_2491_ == 0)
{
v_x_2487_ = v_tail_2490_;
goto _start;
}
else
{
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2493_, lean_object* v_x_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2493_, v_x_2494_);
lean_dec(v_x_2494_);
lean_dec_ref(v_a_2493_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2497_, lean_object* v_a_2498_, lean_object* v_b_2499_){
_start:
{
lean_object* v_size_2500_; lean_object* v_buckets_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2544_; 
v_size_2500_ = lean_ctor_get(v_m_2497_, 0);
v_buckets_2501_ = lean_ctor_get(v_m_2497_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_m_2497_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2503_ = v_m_2497_;
v_isShared_2504_ = v_isSharedCheck_2544_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_buckets_2501_);
lean_inc(v_size_2500_);
lean_dec(v_m_2497_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2544_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v_fold_2509_; uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v_bkt_2518_; uint8_t v___x_2519_; 
v___x_2505_ = lean_array_get_size(v_buckets_2501_);
v___x_2506_ = l_Lean_ExprStructEq_hash(v_a_2498_);
v___x_2507_ = 32ULL;
v___x_2508_ = lean_uint64_shift_right(v___x_2506_, v___x_2507_);
v_fold_2509_ = lean_uint64_xor(v___x_2506_, v___x_2508_);
v___x_2510_ = 16ULL;
v___x_2511_ = lean_uint64_shift_right(v_fold_2509_, v___x_2510_);
v___x_2512_ = lean_uint64_xor(v_fold_2509_, v___x_2511_);
v___x_2513_ = lean_uint64_to_usize(v___x_2512_);
v___x_2514_ = lean_usize_of_nat(v___x_2505_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_sub(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_usize_land(v___x_2513_, v___x_2516_);
v_bkt_2518_ = lean_array_uget_borrowed(v_buckets_2501_, v___x_2517_);
v___x_2519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2498_, v_bkt_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v_size_x27_2521_; lean_object* v___x_2522_; lean_object* v_buckets_x27_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2520_ = lean_unsigned_to_nat(1u);
v_size_x27_2521_ = lean_nat_add(v_size_2500_, v___x_2520_);
lean_dec(v_size_2500_);
lean_inc(v_bkt_2518_);
v___x_2522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2498_);
lean_ctor_set(v___x_2522_, 1, v_b_2499_);
lean_ctor_set(v___x_2522_, 2, v_bkt_2518_);
v_buckets_x27_2523_ = lean_array_uset(v_buckets_2501_, v___x_2517_, v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(4u);
v___x_2525_ = lean_nat_mul(v_size_x27_2521_, v___x_2524_);
v___x_2526_ = lean_unsigned_to_nat(3u);
v___x_2527_ = lean_nat_div(v___x_2525_, v___x_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_array_get_size(v_buckets_x27_2523_);
v___x_2529_ = lean_nat_dec_le(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
if (v___x_2529_ == 0)
{
lean_object* v_val_2530_; lean_object* v___x_2532_; 
v_val_2530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2523_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v_val_2530_);
lean_ctor_set(v___x_2503_, 0, v_size_x27_2521_);
v___x_2532_ = v___x_2503_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_size_x27_2521_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_val_2530_);
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
lean_object* v___x_2535_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v_buckets_x27_2523_);
lean_ctor_set(v___x_2503_, 0, v_size_x27_2521_);
v___x_2535_ = v___x_2503_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_size_x27_2521_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_buckets_x27_2523_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v_buckets_x27_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_inc(v_bkt_2518_);
v___x_2537_ = lean_box(0);
v_buckets_x27_2538_ = lean_array_uset(v_buckets_2501_, v___x_2517_, v___x_2537_);
v___x_2539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2498_, v_b_2499_, v_bkt_2518_);
v___x_2540_ = lean_array_uset(v_buckets_x27_2538_, v___x_2517_, v___x_2539_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2540_);
v___x_2542_ = v___x_2503_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_size_2500_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2545_, lean_object* v_e_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2549_ = lean_st_ref_take(v_a_2545_);
v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2549_, v_e_2546_, v_a_2547_);
v___x_2551_ = lean_st_ref_set(v_a_2545_, v___x_2550_);
v___x_2552_ = lean_box(0);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2553_, lean_object* v_e_2554_, lean_object* v_a_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2553_, v_e_2554_, v_a_2555_);
lean_dec(v_a_2553_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2558_, lean_object* v_x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_apply_1(v_x_2559_, lean_box(0));
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2567_, v_x_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2575_, lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_box(0);
return v___x_2577_;
}
else
{
lean_object* v_key_2578_; lean_object* v_value_2579_; lean_object* v_tail_2580_; uint8_t v___x_2581_; 
v_key_2578_ = lean_ctor_get(v_x_2576_, 0);
v_value_2579_ = lean_ctor_get(v_x_2576_, 1);
v_tail_2580_ = lean_ctor_get(v_x_2576_, 2);
v___x_2581_ = l_Lean_ExprStructEq_beq(v_key_2578_, v_a_2575_);
if (v___x_2581_ == 0)
{
v_x_2576_ = v_tail_2580_;
goto _start;
}
else
{
lean_object* v___x_2583_; 
lean_inc(v_value_2579_);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_value_2579_);
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2584_, lean_object* v_x_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2584_, v_x_2585_);
lean_dec(v_x_2585_);
lean_dec_ref(v_a_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_buckets_2589_; lean_object* v___x_2590_; uint64_t v___x_2591_; uint64_t v___x_2592_; uint64_t v___x_2593_; uint64_t v_fold_2594_; uint64_t v___x_2595_; uint64_t v___x_2596_; uint64_t v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_buckets_2589_ = lean_ctor_get(v_m_2587_, 1);
v___x_2590_ = lean_array_get_size(v_buckets_2589_);
v___x_2591_ = l_Lean_ExprStructEq_hash(v_a_2588_);
v___x_2592_ = 32ULL;
v___x_2593_ = lean_uint64_shift_right(v___x_2591_, v___x_2592_);
v_fold_2594_ = lean_uint64_xor(v___x_2591_, v___x_2593_);
v___x_2595_ = 16ULL;
v___x_2596_ = lean_uint64_shift_right(v_fold_2594_, v___x_2595_);
v___x_2597_ = lean_uint64_xor(v_fold_2594_, v___x_2596_);
v___x_2598_ = lean_uint64_to_usize(v___x_2597_);
v___x_2599_ = lean_usize_of_nat(v___x_2590_);
v___x_2600_ = ((size_t)1ULL);
v___x_2601_ = lean_usize_sub(v___x_2599_, v___x_2600_);
v___x_2602_ = lean_usize_land(v___x_2598_, v___x_2601_);
v___x_2603_ = lean_array_uget_borrowed(v_buckets_2589_, v___x_2602_);
v___x_2604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2588_, v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2605_, v_a_2606_);
lean_dec_ref(v_a_2606_);
lean_dec_ref(v_m_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2608_, lean_object* v___y_2609_, lean_object* v_b_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_apply_7(v_k_2608_, v_b_2610_, v___y_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, lean_box(0));
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2617_, lean_object* v___y_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2617_, v___y_2618_, v_b_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2626_, uint8_t v_bi_2627_, lean_object* v_type_2628_, lean_object* v_k_2629_, uint8_t v_kind_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___f_2637_; lean_object* v___x_2638_; 
v___f_2637_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2637_, 0, v_k_2629_);
lean_closure_set(v___f_2637_, 1, v___y_2631_);
v___x_2638_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2626_, v_bi_2627_, v_type_2628_, v___f_2637_, v_kind_2630_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2638_) == 0)
{
return v___x_2638_;
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2647_, lean_object* v_bi_2648_, lean_object* v_type_2649_, lean_object* v_k_2650_, lean_object* v_kind_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v_bi_boxed_2658_; uint8_t v_kind_boxed_2659_; lean_object* v_res_2660_; 
v_bi_boxed_2658_ = lean_unbox(v_bi_2648_);
v_kind_boxed_2659_ = lean_unbox(v_kind_2651_);
v_res_2660_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2647_, v_bi_boxed_2658_, v_type_2649_, v_k_2650_, v_kind_boxed_2659_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2661_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2675_, lean_object* v_type_2676_, lean_object* v_val_2677_, lean_object* v_k_2678_, uint8_t v_nondep_2679_, uint8_t v_kind_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___f_2687_; lean_object* v___x_2688_; 
v___f_2687_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2687_, 0, v_k_2678_);
lean_closure_set(v___f_2687_, 1, v___y_2681_);
v___x_2688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2675_, v_type_2676_, v_val_2677_, v___f_2687_, v_nondep_2679_, v_kind_2680_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2688_) == 0)
{
return v___x_2688_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2697_, lean_object* v_type_2698_, lean_object* v_val_2699_, lean_object* v_k_2700_, lean_object* v_nondep_2701_, lean_object* v_kind_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v_nondep_boxed_2709_; uint8_t v_kind_boxed_2710_; lean_object* v_res_2711_; 
v_nondep_boxed_2709_ = lean_unbox(v_nondep_2701_);
v_kind_boxed_2710_ = lean_unbox(v_kind_2702_);
v_res_2711_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2697_, v_type_2698_, v_val_2699_, v_k_2700_, v_nondep_boxed_2709_, v_kind_boxed_2710_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v_res_2711_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = l_Lean_maxRecDepthErrorMessage;
v___x_2718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2720_ = l_Lean_MessageData_ofFormat(v___x_2719_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2722_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2723_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_ref_2724_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2729_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___y_2740_; lean_object* v_fileName_2749_; lean_object* v_fileMap_2750_; lean_object* v_options_2751_; lean_object* v_currRecDepth_2752_; lean_object* v_maxRecDepth_2753_; lean_object* v_ref_2754_; lean_object* v_currNamespace_2755_; lean_object* v_openDecls_2756_; lean_object* v_initHeartbeats_2757_; lean_object* v_maxHeartbeats_2758_; lean_object* v_quotContext_2759_; lean_object* v_currMacroScope_2760_; uint8_t v_diag_2761_; lean_object* v_cancelTk_x3f_2762_; uint8_t v_suppressElabErrors_2763_; lean_object* v_inheritedTraceOptions_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2776_; 
v_fileName_2749_ = lean_ctor_get(v___y_2736_, 0);
v_fileMap_2750_ = lean_ctor_get(v___y_2736_, 1);
v_options_2751_ = lean_ctor_get(v___y_2736_, 2);
v_currRecDepth_2752_ = lean_ctor_get(v___y_2736_, 3);
v_maxRecDepth_2753_ = lean_ctor_get(v___y_2736_, 4);
v_ref_2754_ = lean_ctor_get(v___y_2736_, 5);
v_currNamespace_2755_ = lean_ctor_get(v___y_2736_, 6);
v_openDecls_2756_ = lean_ctor_get(v___y_2736_, 7);
v_initHeartbeats_2757_ = lean_ctor_get(v___y_2736_, 8);
v_maxHeartbeats_2758_ = lean_ctor_get(v___y_2736_, 9);
v_quotContext_2759_ = lean_ctor_get(v___y_2736_, 10);
v_currMacroScope_2760_ = lean_ctor_get(v___y_2736_, 11);
v_diag_2761_ = lean_ctor_get_uint8(v___y_2736_, sizeof(void*)*14);
v_cancelTk_x3f_2762_ = lean_ctor_get(v___y_2736_, 12);
v_suppressElabErrors_2763_ = lean_ctor_get_uint8(v___y_2736_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2764_ = lean_ctor_get(v___y_2736_, 13);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___y_2736_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2766_ = v___y_2736_;
v_isShared_2767_ = v_isSharedCheck_2776_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_inheritedTraceOptions_2764_);
lean_inc(v_cancelTk_x3f_2762_);
lean_inc(v_currMacroScope_2760_);
lean_inc(v_quotContext_2759_);
lean_inc(v_maxHeartbeats_2758_);
lean_inc(v_initHeartbeats_2757_);
lean_inc(v_openDecls_2756_);
lean_inc(v_currNamespace_2755_);
lean_inc(v_ref_2754_);
lean_inc(v_maxRecDepth_2753_);
lean_inc(v_currRecDepth_2752_);
lean_inc(v_options_2751_);
lean_inc(v_fileMap_2750_);
lean_inc(v_fileName_2749_);
lean_dec(v___y_2736_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2776_;
goto v_resetjp_2765_;
}
v___jp_2739_:
{
if (lean_obj_tag(v___y_2740_) == 0)
{
return v___y_2740_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_a_2741_ = lean_ctor_get(v___y_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___y_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___y_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___y_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
v_resetjp_2765_:
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_nat_dec_eq(v_currRecDepth_2752_, v_maxRecDepth_2753_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2770_ = lean_nat_add(v_currRecDepth_2752_, v___x_2769_);
lean_dec(v_currRecDepth_2752_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 3, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_fileName_2749_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_fileMap_2750_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_options_2751_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v_maxRecDepth_2753_);
lean_ctor_set(v_reuseFailAlloc_2774_, 5, v_ref_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 6, v_currNamespace_2755_);
lean_ctor_set(v_reuseFailAlloc_2774_, 7, v_openDecls_2756_);
lean_ctor_set(v_reuseFailAlloc_2774_, 8, v_initHeartbeats_2757_);
lean_ctor_set(v_reuseFailAlloc_2774_, 9, v_maxHeartbeats_2758_);
lean_ctor_set(v_reuseFailAlloc_2774_, 10, v_quotContext_2759_);
lean_ctor_set(v_reuseFailAlloc_2774_, 11, v_currMacroScope_2760_);
lean_ctor_set(v_reuseFailAlloc_2774_, 12, v_cancelTk_x3f_2762_);
lean_ctor_set(v_reuseFailAlloc_2774_, 13, v_inheritedTraceOptions_2764_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, sizeof(void*)*14, v_diag_2761_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, sizeof(void*)*14 + 1, v_suppressElabErrors_2763_);
v___x_2772_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_apply_6(v_x_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___x_2772_, v___y_2737_, lean_box(0));
v___y_2740_ = v___x_2773_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2775_; 
lean_del_object(v___x_2766_);
lean_dec_ref(v_inheritedTraceOptions_2764_);
lean_dec(v_cancelTk_x3f_2762_);
lean_dec(v_currMacroScope_2760_);
lean_dec(v_quotContext_2759_);
lean_dec(v_maxHeartbeats_2758_);
lean_dec(v_initHeartbeats_2757_);
lean_dec(v_openDecls_2756_);
lean_dec(v_currNamespace_2755_);
lean_dec(v_maxRecDepth_2753_);
lean_dec(v_currRecDepth_2752_);
lean_dec_ref(v_options_2751_);
lean_dec_ref(v_fileMap_2750_);
lean_dec_ref(v_fileName_2749_);
lean_dec(v___y_2737_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v_x_2732_);
v___x_2775_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2754_);
v___y_2740_ = v___x_2775_;
goto v___jp_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2787_, lean_object* v_pre_2788_, lean_object* v_post_2789_, uint8_t v_usedLetOnly_2790_, uint8_t v_skipConstInApp_2791_, uint8_t v_skipInstances_2792_, lean_object* v_body_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_array_push(v_fvars_2787_, v_x_2794_);
v___x_2802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2788_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2801_, v_body_2793_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2803_, lean_object* v_pre_2804_, lean_object* v_post_2805_, lean_object* v_usedLetOnly_2806_, lean_object* v_skipConstInApp_2807_, lean_object* v_skipInstances_2808_, lean_object* v_body_2809_, lean_object* v_x_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v_usedLetOnly_boxed_2817_; uint8_t v_skipConstInApp_boxed_2818_; uint8_t v_skipInstances_boxed_2819_; lean_object* v_res_2820_; 
v_usedLetOnly_boxed_2817_ = lean_unbox(v_usedLetOnly_2806_);
v_skipConstInApp_boxed_2818_ = lean_unbox(v_skipConstInApp_2807_);
v_skipInstances_boxed_2819_ = lean_unbox(v_skipInstances_2808_);
v_res_2820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2803_, v_pre_2804_, v_post_2805_, v_usedLetOnly_boxed_2817_, v_skipConstInApp_boxed_2818_, v_skipInstances_boxed_2819_, v_body_2809_, v_x_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2821_, lean_object* v_post_2822_, uint8_t v_usedLetOnly_2823_, uint8_t v_skipConstInApp_2824_, uint8_t v_skipInstances_2825_, lean_object* v_e_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
lean_inc_ref(v_post_2822_);
lean_inc(v___y_2831_);
lean_inc_ref(v___y_2830_);
lean_inc(v___y_2829_);
lean_inc_ref(v___y_2828_);
lean_inc_ref(v_e_2826_);
v___x_2833_ = lean_apply_6(v_post_2822_, v_e_2826_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, lean_box(0));
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2852_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2852_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2852_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
switch(lean_obj_tag(v_a_2834_))
{
case 0:
{
lean_object* v_e_2838_; lean_object* v___x_2840_; 
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_e_2826_);
lean_dec_ref(v_post_2822_);
lean_dec_ref(v_pre_2821_);
v_e_2838_ = lean_ctor_get(v_a_2834_, 0);
lean_inc_ref(v_e_2838_);
lean_dec_ref(v_a_2834_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_e_2838_);
v___x_2840_ = v___x_2836_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_e_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
case 1:
{
lean_object* v_e_2842_; lean_object* v___x_2843_; 
lean_del_object(v___x_2836_);
lean_dec_ref(v_e_2826_);
v_e_2842_ = lean_ctor_get(v_a_2834_, 0);
lean_inc_ref(v_e_2842_);
lean_dec_ref(v_a_2834_);
v___x_2843_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2821_, v_post_2822_, v_usedLetOnly_2823_, v_skipConstInApp_2824_, v_skipInstances_2825_, v_e_2842_, v_a_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2843_;
}
default: 
{
lean_object* v_e_x3f_2844_; 
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_post_2822_);
lean_dec_ref(v_pre_2821_);
v_e_x3f_2844_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_e_x3f_2844_);
lean_dec_ref(v_a_2834_);
if (lean_obj_tag(v_e_x3f_2844_) == 0)
{
lean_object* v___x_2846_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_e_2826_);
v___x_2846_ = v___x_2836_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_e_2826_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
else
{
lean_object* v_val_2848_; lean_object* v___x_2850_; 
lean_dec_ref(v_e_2826_);
v_val_2848_ = lean_ctor_get(v_e_x3f_2844_, 0);
lean_inc(v_val_2848_);
lean_dec_ref(v_e_x3f_2844_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v_val_2848_);
v___x_2850_ = v___x_2836_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_val_2848_);
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
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_e_2826_);
lean_dec_ref(v_post_2822_);
lean_dec_ref(v_pre_2821_);
v_a_2853_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2833_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2833_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2861_, lean_object* v_post_2862_, uint8_t v_usedLetOnly_2863_, uint8_t v_skipConstInApp_2864_, uint8_t v_skipInstances_2865_, lean_object* v_fvars_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
if (lean_obj_tag(v_e_2867_) == 6)
{
lean_object* v_binderName_2874_; lean_object* v_binderType_2875_; lean_object* v_body_2876_; uint8_t v_binderInfo_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_binderName_2874_ = lean_ctor_get(v_e_2867_, 0);
lean_inc(v_binderName_2874_);
v_binderType_2875_ = lean_ctor_get(v_e_2867_, 1);
lean_inc_ref(v_binderType_2875_);
v_body_2876_ = lean_ctor_get(v_e_2867_, 2);
lean_inc_ref(v_body_2876_);
v_binderInfo_2877_ = lean_ctor_get_uint8(v_e_2867_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2867_);
v___x_2878_ = lean_expr_instantiate_rev(v_binderType_2875_, v_fvars_2866_);
lean_dec_ref(v_binderType_2875_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v_post_2862_);
lean_inc_ref(v_pre_2861_);
v___x_2879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2861_, v_post_2862_, v_usedLetOnly_2863_, v_skipConstInApp_2864_, v_skipInstances_2865_, v___x_2878_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___f_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_box(v_usedLetOnly_2863_);
v___x_2882_ = lean_box(v_skipConstInApp_2864_);
v___x_2883_ = lean_box(v_skipInstances_2865_);
v___f_2884_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2884_, 0, v_fvars_2866_);
lean_closure_set(v___f_2884_, 1, v_pre_2861_);
lean_closure_set(v___f_2884_, 2, v_post_2862_);
lean_closure_set(v___f_2884_, 3, v___x_2881_);
lean_closure_set(v___f_2884_, 4, v___x_2882_);
lean_closure_set(v___f_2884_, 5, v___x_2883_);
lean_closure_set(v___f_2884_, 6, v_body_2876_);
v___x_2885_ = 0;
v___x_2886_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2874_, v_binderInfo_2877_, v_a_2880_, v___f_2884_, v___x_2885_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
return v___x_2886_;
}
else
{
lean_dec_ref(v_body_2876_);
lean_dec(v_binderName_2874_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_fvars_2866_);
lean_dec_ref(v_post_2862_);
lean_dec_ref(v_pre_2861_);
return v___x_2879_;
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_expr_instantiate_rev(v_e_2867_, v_fvars_2866_);
lean_dec_ref(v_e_2867_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
lean_inc(v___y_2870_);
lean_inc_ref(v___y_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v_post_2862_);
lean_inc_ref(v_pre_2861_);
v___x_2888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2861_, v_post_2862_, v_usedLetOnly_2863_, v_skipConstInApp_2864_, v_skipInstances_2865_, v___x_2887_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; uint8_t v___x_2890_; uint8_t v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = 0;
v___x_2891_ = 1;
v___x_2892_ = 1;
v___x_2893_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2866_, v_a_2889_, v___x_2890_, v_usedLetOnly_2863_, v___x_2890_, v___x_2891_, v___x_2892_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec_ref(v_fvars_2866_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2861_, v_post_2862_, v_usedLetOnly_2863_, v_skipConstInApp_2864_, v_skipInstances_2865_, v_a_2894_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
return v___x_2895_;
}
else
{
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_post_2862_);
lean_dec_ref(v_pre_2861_);
return v___x_2893_;
}
}
else
{
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_fvars_2866_);
lean_dec_ref(v_post_2862_);
lean_dec_ref(v_pre_2861_);
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2896_, lean_object* v_pre_2897_, lean_object* v_post_2898_, uint8_t v_usedLetOnly_2899_, uint8_t v_skipConstInApp_2900_, uint8_t v_skipInstances_2901_, lean_object* v_body_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_array_push(v_fvars_2896_, v_x_2903_);
v___x_2911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2897_, v_post_2898_, v_usedLetOnly_2899_, v_skipConstInApp_2900_, v_skipInstances_2901_, v___x_2910_, v_body_2902_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2912_, lean_object* v_pre_2913_, lean_object* v_post_2914_, lean_object* v_usedLetOnly_2915_, lean_object* v_skipConstInApp_2916_, lean_object* v_skipInstances_2917_, lean_object* v_body_2918_, lean_object* v_x_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
uint8_t v_usedLetOnly_boxed_2926_; uint8_t v_skipConstInApp_boxed_2927_; uint8_t v_skipInstances_boxed_2928_; lean_object* v_res_2929_; 
v_usedLetOnly_boxed_2926_ = lean_unbox(v_usedLetOnly_2915_);
v_skipConstInApp_boxed_2927_ = lean_unbox(v_skipConstInApp_2916_);
v_skipInstances_boxed_2928_ = lean_unbox(v_skipInstances_2917_);
v_res_2929_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2912_, v_pre_2913_, v_post_2914_, v_usedLetOnly_boxed_2926_, v_skipConstInApp_boxed_2927_, v_skipInstances_boxed_2928_, v_body_2918_, v_x_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2930_, lean_object* v_post_2931_, uint8_t v_usedLetOnly_2932_, uint8_t v_skipConstInApp_2933_, uint8_t v_skipInstances_2934_, lean_object* v_fvars_2935_, lean_object* v_e_2936_, lean_object* v_a_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
if (lean_obj_tag(v_e_2936_) == 8)
{
lean_object* v_declName_2943_; lean_object* v_type_2944_; lean_object* v_value_2945_; lean_object* v_body_2946_; uint8_t v_nondep_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_declName_2943_ = lean_ctor_get(v_e_2936_, 0);
lean_inc(v_declName_2943_);
v_type_2944_ = lean_ctor_get(v_e_2936_, 1);
lean_inc_ref(v_type_2944_);
v_value_2945_ = lean_ctor_get(v_e_2936_, 2);
lean_inc_ref(v_value_2945_);
v_body_2946_ = lean_ctor_get(v_e_2936_, 3);
lean_inc_ref(v_body_2946_);
v_nondep_2947_ = lean_ctor_get_uint8(v_e_2936_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2936_);
v___x_2948_ = lean_expr_instantiate_rev(v_type_2944_, v_fvars_2935_);
lean_dec_ref(v_type_2944_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_post_2931_);
lean_inc_ref(v_pre_2930_);
v___x_2949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v_skipInstances_2934_, v___x_2948_, v_a_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = lean_expr_instantiate_rev(v_value_2945_, v_fvars_2935_);
lean_dec_ref(v_value_2945_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_post_2931_);
lean_inc_ref(v_pre_2930_);
v___x_2952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v_skipInstances_2934_, v___x_2951_, v_a_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___f_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
v___x_2954_ = lean_box(v_usedLetOnly_2932_);
v___x_2955_ = lean_box(v_skipConstInApp_2933_);
v___x_2956_ = lean_box(v_skipInstances_2934_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2957_, 0, v_fvars_2935_);
lean_closure_set(v___f_2957_, 1, v_pre_2930_);
lean_closure_set(v___f_2957_, 2, v_post_2931_);
lean_closure_set(v___f_2957_, 3, v___x_2954_);
lean_closure_set(v___f_2957_, 4, v___x_2955_);
lean_closure_set(v___f_2957_, 5, v___x_2956_);
lean_closure_set(v___f_2957_, 6, v_body_2946_);
v___x_2958_ = 0;
v___x_2959_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2943_, v_a_2950_, v_a_2953_, v___f_2957_, v_nondep_2947_, v___x_2958_, v_a_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
return v___x_2959_;
}
else
{
lean_dec(v_a_2950_);
lean_dec_ref(v_body_2946_);
lean_dec(v_declName_2943_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_fvars_2935_);
lean_dec_ref(v_post_2931_);
lean_dec_ref(v_pre_2930_);
return v___x_2952_;
}
}
else
{
lean_dec_ref(v_body_2946_);
lean_dec_ref(v_value_2945_);
lean_dec(v_declName_2943_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_fvars_2935_);
lean_dec_ref(v_post_2931_);
lean_dec_ref(v_pre_2930_);
return v___x_2949_;
}
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_expr_instantiate_rev(v_e_2936_, v_fvars_2935_);
lean_dec_ref(v_e_2936_);
lean_inc(v___y_2941_);
lean_inc_ref(v___y_2940_);
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v_a_2937_);
lean_inc_ref(v_post_2931_);
lean_inc_ref(v_pre_2930_);
v___x_2961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v_skipInstances_2934_, v___x_2960_, v_a_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; uint8_t v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = 0;
v___x_2964_ = 1;
v___x_2965_ = l_Lean_Meta_mkLetFVars(v_fvars_2935_, v_a_2962_, v_usedLetOnly_2932_, v___x_2963_, v___x_2964_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec_ref(v_fvars_2935_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2930_, v_post_2931_, v_usedLetOnly_2932_, v_skipConstInApp_2933_, v_skipInstances_2934_, v_a_2966_, v_a_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
return v___x_2967_;
}
else
{
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_post_2931_);
lean_dec_ref(v_pre_2930_);
return v___x_2965_;
}
}
else
{
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_fvars_2935_);
lean_dec_ref(v_post_2931_);
lean_dec_ref(v_pre_2930_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2968_, lean_object* v_post_2969_, uint8_t v_usedLetOnly_2970_, uint8_t v_skipConstInApp_2971_, uint8_t v_skipInstances_2972_, size_t v_sz_2973_, size_t v_i_2974_, lean_object* v_bs_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v_post_2969_);
lean_dec_ref(v_pre_2968_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_bs_2975_);
return v___x_2983_;
}
else
{
lean_object* v_v_2984_; lean_object* v___x_2985_; 
v_v_2984_ = lean_array_uget_borrowed(v_bs_2975_, v_i_2974_);
lean_inc(v___y_2980_);
lean_inc_ref(v___y_2979_);
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
lean_inc(v___y_2976_);
lean_inc(v_v_2984_);
lean_inc_ref(v_post_2969_);
lean_inc_ref(v_pre_2968_);
v___x_2985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2968_, v_post_2969_, v_usedLetOnly_2970_, v_skipConstInApp_2971_, v_skipInstances_2972_, v_v_2984_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v_bs_x27_2988_; size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = lean_unsigned_to_nat(0u);
v_bs_x27_2988_ = lean_array_uset(v_bs_2975_, v_i_2974_, v___x_2987_);
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2974_, v___x_2989_);
v___x_2991_ = lean_array_uset(v_bs_x27_2988_, v_i_2974_, v_a_2986_);
v_i_2974_ = v___x_2990_;
v_bs_2975_ = v___x_2991_;
goto _start;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v_bs_2975_);
lean_dec_ref(v_post_2969_);
lean_dec_ref(v_pre_2968_);
v_a_2993_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2985_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2985_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3001_, lean_object* v_post_3002_, uint8_t v_usedLetOnly_3003_, uint8_t v_skipConstInApp_3004_, uint8_t v_skipInstances_3005_, lean_object* v___x_3006_, lean_object* v___y_3007_, lean_object* v_b_3008_, lean_object* v_a_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3001_, v_post_3002_, v_usedLetOnly_3003_, v_skipConstInApp_3004_, v_skipInstances_3005_, v___x_3006_, v___y_3007_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3025_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = lean_array_fset(v_b_3008_, v_a_3009_, v_a_3016_);
v___x_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_b_3008_);
v_a_3026_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3015_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3015_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3034_, lean_object* v_post_3035_, lean_object* v_usedLetOnly_3036_, lean_object* v_skipConstInApp_3037_, lean_object* v_skipInstances_3038_, lean_object* v___x_3039_, lean_object* v___y_3040_, lean_object* v_b_3041_, lean_object* v_a_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v_usedLetOnly_boxed_3048_; uint8_t v_skipConstInApp_boxed_3049_; uint8_t v_skipInstances_boxed_3050_; lean_object* v_res_3051_; 
v_usedLetOnly_boxed_3048_ = lean_unbox(v_usedLetOnly_3036_);
v_skipConstInApp_boxed_3049_ = lean_unbox(v_skipConstInApp_3037_);
v_skipInstances_boxed_3050_ = lean_unbox(v_skipInstances_3038_);
v_res_3051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3034_, v_post_3035_, v_usedLetOnly_boxed_3048_, v_skipConstInApp_boxed_3049_, v_skipInstances_boxed_3050_, v___x_3039_, v___y_3040_, v_b_3041_, v_a_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v_a_3042_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3052_, lean_object* v___x_3053_, lean_object* v_pre_3054_, lean_object* v_post_3055_, uint8_t v_usedLetOnly_3056_, uint8_t v_skipConstInApp_3057_, uint8_t v_skipInstances_3058_, lean_object* v_a_3059_, lean_object* v_b_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___y_3068_; uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_lt(v_a_3059_, v_upperBound_3052_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v_a_3059_);
lean_dec_ref(v_post_3055_);
lean_dec_ref(v_pre_3054_);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_b_3060_);
return v___x_3092_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = lean_array_fget_borrowed(v_b_3060_, v_a_3059_);
v___x_3094_ = lean_array_get_size(v___x_3053_);
v___x_3095_ = lean_nat_dec_lt(v_a_3059_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; 
lean_inc(v___x_3093_);
v___x_3096_ = lean_box(v_usedLetOnly_3056_);
v___x_3097_ = lean_box(v_skipConstInApp_3057_);
v___x_3098_ = lean_box(v_skipInstances_3058_);
lean_inc(v_a_3059_);
lean_inc(v___y_3061_);
lean_inc_ref(v_post_3055_);
lean_inc_ref(v_pre_3054_);
v___f_3099_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3099_, 0, v_pre_3054_);
lean_closure_set(v___f_3099_, 1, v_post_3055_);
lean_closure_set(v___f_3099_, 2, v___x_3096_);
lean_closure_set(v___f_3099_, 3, v___x_3097_);
lean_closure_set(v___f_3099_, 4, v___x_3098_);
lean_closure_set(v___f_3099_, 5, v___x_3093_);
lean_closure_set(v___f_3099_, 6, v___y_3061_);
lean_closure_set(v___f_3099_, 7, v_b_3060_);
lean_closure_set(v___f_3099_, 8, v_a_3059_);
v___y_3068_ = v___f_3099_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3100_; uint8_t v_isInstance_3101_; 
v___x_3100_ = lean_array_fget_borrowed(v___x_3053_, v_a_3059_);
v_isInstance_3101_ = lean_ctor_get_uint8(v___x_3100_, sizeof(void*)*1 + 4);
if (v_isInstance_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; 
lean_inc(v___x_3093_);
v___x_3102_ = lean_box(v_usedLetOnly_3056_);
v___x_3103_ = lean_box(v_skipConstInApp_3057_);
v___x_3104_ = lean_box(v_skipInstances_3058_);
lean_inc(v_a_3059_);
lean_inc(v___y_3061_);
lean_inc_ref(v_post_3055_);
lean_inc_ref(v_pre_3054_);
v___f_3105_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3105_, 0, v_pre_3054_);
lean_closure_set(v___f_3105_, 1, v_post_3055_);
lean_closure_set(v___f_3105_, 2, v___x_3102_);
lean_closure_set(v___f_3105_, 3, v___x_3103_);
lean_closure_set(v___f_3105_, 4, v___x_3104_);
lean_closure_set(v___f_3105_, 5, v___x_3093_);
lean_closure_set(v___f_3105_, 6, v___y_3061_);
lean_closure_set(v___f_3105_, 7, v_b_3060_);
lean_closure_set(v___f_3105_, 8, v_a_3059_);
v___y_3068_ = v___f_3105_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3106_; lean_object* v___f_3107_; 
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_b_3060_);
v___f_3107_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3107_, 0, v___x_3106_);
v___y_3068_ = v___f_3107_;
goto v___jp_3067_;
}
}
}
v___jp_3067_:
{
lean_object* v___x_3069_; 
lean_inc(v___y_3065_);
lean_inc_ref(v___y_3064_);
lean_inc(v___y_3063_);
lean_inc_ref(v___y_3062_);
v___x_3069_ = lean_apply_5(v___y_3068_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, lean_box(0));
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3082_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3082_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
if (lean_obj_tag(v_a_3070_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; 
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v_a_3059_);
lean_dec_ref(v_post_3055_);
lean_dec_ref(v_pre_3054_);
v_a_3074_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v_a_3070_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_a_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3074_);
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
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_del_object(v___x_3072_);
v_a_3078_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v_a_3070_);
v___x_3079_ = lean_unsigned_to_nat(1u);
v___x_3080_ = lean_nat_add(v_a_3059_, v___x_3079_);
lean_dec(v_a_3059_);
v_a_3059_ = v___x_3080_;
v_b_3060_ = v_a_3078_;
goto _start;
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v_a_3059_);
lean_dec_ref(v_post_3055_);
lean_dec_ref(v_pre_3054_);
v_a_3083_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3069_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3069_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3108_, lean_object* v_pre_3109_, lean_object* v_post_3110_, uint8_t v_usedLetOnly_3111_, uint8_t v_skipConstInApp_3112_, lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_f_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; 
if (lean_obj_tag(v_x_3113_) == 5)
{
lean_object* v_fn_3171_; lean_object* v_arg_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_fn_3171_ = lean_ctor_get(v_x_3113_, 0);
lean_inc_ref(v_fn_3171_);
v_arg_3172_ = lean_ctor_get(v_x_3113_, 1);
lean_inc_ref(v_arg_3172_);
lean_dec_ref(v_x_3113_);
v___x_3173_ = lean_array_set(v_x_3114_, v_x_3115_, v_arg_3172_);
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = lean_nat_sub(v_x_3115_, v___x_3174_);
lean_dec(v_x_3115_);
v_x_3113_ = v_fn_3171_;
v_x_3114_ = v___x_3173_;
v_x_3115_ = v___x_3175_;
goto _start;
}
else
{
lean_dec(v_x_3115_);
if (v_skipConstInApp_3112_ == 0)
{
goto v___jp_3168_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = l_Lean_Expr_isConst(v_x_3113_);
if (v___x_3177_ == 0)
{
goto v___jp_3168_;
}
else
{
v_f_3123_ = v_x_3113_;
v___y_3124_ = v___y_3116_;
v___y_3125_ = v___y_3117_;
v___y_3126_ = v___y_3118_;
v___y_3127_ = v___y_3119_;
v___y_3128_ = v___y_3120_;
goto v___jp_3122_;
}
}
}
v___jp_3122_:
{
if (v_skipInstances_3108_ == 0)
{
size_t v_sz_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v_sz_3129_ = lean_array_size(v_x_3114_);
v___x_3130_ = ((size_t)0ULL);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3124_);
lean_inc_ref(v_post_3110_);
lean_inc_ref(v_pre_3109_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3109_, v_post_3110_, v_usedLetOnly_3111_, v_skipConstInApp_3112_, v_skipInstances_3108_, v_sz_3129_, v___x_3130_, v_x_3114_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = l_Lean_mkAppN(v_f_3123_, v_a_3132_);
lean_dec(v_a_3132_);
v___x_3134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3109_, v_post_3110_, v_usedLetOnly_3111_, v_skipConstInApp_3112_, v_skipInstances_3108_, v___x_3133_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3134_;
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_f_3123_);
lean_dec_ref(v_post_3110_);
lean_dec_ref(v_pre_3109_);
v_a_3135_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3131_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3131_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_array_get_size(v_x_3114_);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
lean_inc_ref(v_f_3123_);
v___x_3144_ = l_Lean_Meta_getFunInfoNArgs(v_f_3123_, v___x_3143_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v_paramInfo_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
v_paramInfo_3146_ = lean_ctor_get(v_a_3145_, 0);
lean_inc_ref(v_paramInfo_3146_);
lean_dec(v_a_3145_);
v___x_3147_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3124_);
lean_inc_ref(v_post_3110_);
lean_inc_ref(v_pre_3109_);
v___x_3148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3143_, v_paramInfo_3146_, v_pre_3109_, v_post_3110_, v_usedLetOnly_3111_, v_skipConstInApp_3112_, v_skipInstances_3108_, v___x_3147_, v_x_3114_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec_ref(v_paramInfo_3146_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3148_);
v___x_3150_ = l_Lean_mkAppN(v_f_3123_, v_a_3149_);
lean_dec(v_a_3149_);
v___x_3151_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3109_, v_post_3110_, v_usedLetOnly_3111_, v_skipConstInApp_3112_, v_skipInstances_3108_, v___x_3150_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3151_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_f_3123_);
lean_dec_ref(v_post_3110_);
lean_dec_ref(v_pre_3109_);
v_a_3152_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3148_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3148_);
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
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_f_3123_);
lean_dec_ref(v_x_3114_);
lean_dec_ref(v_post_3110_);
lean_dec_ref(v_pre_3109_);
v_a_3160_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3144_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3144_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3169_; 
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
lean_inc(v___y_3118_);
lean_inc_ref(v___y_3117_);
lean_inc(v___y_3116_);
lean_inc_ref(v_post_3110_);
lean_inc_ref(v_pre_3109_);
v___x_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3109_, v_post_3110_, v_usedLetOnly_3111_, v_skipConstInApp_3112_, v_skipInstances_3108_, v_x_3113_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3169_);
v_f_3123_ = v_a_3170_;
v___y_3124_ = v___y_3116_;
v___y_3125_ = v___y_3117_;
v___y_3126_ = v___y_3118_;
v___y_3127_ = v___y_3119_;
v___y_3128_ = v___y_3120_;
goto v___jp_3122_;
}
else
{
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v_x_3114_);
lean_dec_ref(v_post_3110_);
lean_dec_ref(v_pre_3109_);
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v_pre_3178_, lean_object* v_e_3179_, lean_object* v_post_3180_, uint8_t v_usedLetOnly_3181_, uint8_t v_skipConstInApp_3182_, uint8_t v_skipInstances_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
lean_inc_ref(v_pre_3178_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc_ref(v_e_3179_);
v___x_3190_ = lean_apply_6(v_pre_3178_, v_e_3179_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, lean_box(0));
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3239_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3239_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3239_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___y_3196_; 
switch(lean_obj_tag(v_a_3191_))
{
case 0:
{
lean_object* v_e_3231_; lean_object* v___x_3233_; 
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v_post_3180_);
lean_dec_ref(v_e_3179_);
lean_dec_ref(v_pre_3178_);
v_e_3231_ = lean_ctor_get(v_a_3191_, 0);
lean_inc_ref(v_e_3231_);
lean_dec_ref(v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v_e_3231_);
v___x_3233_ = v___x_3193_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_e_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
case 1:
{
lean_object* v_e_3235_; lean_object* v___x_3236_; 
lean_del_object(v___x_3193_);
lean_dec_ref(v_e_3179_);
v_e_3235_ = lean_ctor_get(v_a_3191_, 0);
lean_inc_ref(v_e_3235_);
lean_dec_ref(v_a_3191_);
v___x_3236_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v_e_3235_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3236_;
}
default: 
{
lean_object* v_e_x3f_3237_; 
lean_del_object(v___x_3193_);
v_e_x3f_3237_ = lean_ctor_get(v_a_3191_, 0);
lean_inc(v_e_x3f_3237_);
lean_dec_ref(v_a_3191_);
if (lean_obj_tag(v_e_x3f_3237_) == 0)
{
v___y_3196_ = v_e_3179_;
goto v___jp_3195_;
}
else
{
lean_object* v_val_3238_; 
lean_dec_ref(v_e_3179_);
v_val_3238_ = lean_ctor_get(v_e_x3f_3237_, 0);
lean_inc(v_val_3238_);
lean_dec_ref(v_e_x3f_3237_);
v___y_3196_ = v_val_3238_;
goto v___jp_3195_;
}
}
}
v___jp_3195_:
{
switch(lean_obj_tag(v___y_3196_))
{
case 7:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3198_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___x_3197_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3198_;
}
case 6:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___x_3199_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3200_;
}
case 8:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___x_3201_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3202_;
}
case 5:
{
lean_object* v_dummy_3203_; lean_object* v_nargs_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_dummy_3203_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3204_ = l_Lean_Expr_getAppNumArgs(v___y_3196_);
lean_inc(v_nargs_3204_);
v___x_3205_ = lean_mk_array(v_nargs_3204_, v_dummy_3203_);
v___x_3206_ = lean_unsigned_to_nat(1u);
v___x_3207_ = lean_nat_sub(v_nargs_3204_, v___x_3206_);
lean_dec(v_nargs_3204_);
v___x_3208_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3183_, v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v___y_3196_, v___x_3205_, v___x_3207_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3208_;
}
case 10:
{
lean_object* v_data_3209_; lean_object* v_expr_3210_; lean_object* v___x_3211_; 
v_data_3209_ = lean_ctor_get(v___y_3196_, 0);
v_expr_3210_ = lean_ctor_get(v___y_3196_, 1);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v_expr_3210_);
lean_inc_ref(v_post_3180_);
lean_inc_ref(v_pre_3178_);
v___x_3211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v_expr_3210_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; size_t v___x_3213_; size_t v___x_3214_; uint8_t v___x_3215_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = lean_ptr_addr(v_expr_3210_);
v___x_3214_ = lean_ptr_addr(v_a_3212_);
v___x_3215_ = lean_usize_dec_eq(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_inc(v_data_3209_);
lean_dec_ref(v___y_3196_);
v___x_3216_ = l_Lean_Expr_mdata___override(v_data_3209_, v_a_3212_);
v___x_3217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___x_3216_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; 
lean_dec(v_a_3212_);
v___x_3218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3218_;
}
}
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v_post_3180_);
lean_dec_ref(v_pre_3178_);
return v___x_3211_;
}
}
case 11:
{
lean_object* v_typeName_3219_; lean_object* v_idx_3220_; lean_object* v_struct_3221_; lean_object* v___x_3222_; 
v_typeName_3219_ = lean_ctor_get(v___y_3196_, 0);
v_idx_3220_ = lean_ctor_get(v___y_3196_, 1);
v_struct_3221_ = lean_ctor_get(v___y_3196_, 2);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v_struct_3221_);
lean_inc_ref(v_post_3180_);
lean_inc_ref(v_pre_3178_);
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v_struct_3221_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; size_t v___x_3224_; size_t v___x_3225_; uint8_t v___x_3226_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = lean_ptr_addr(v_struct_3221_);
v___x_3225_ = lean_ptr_addr(v_a_3223_);
v___x_3226_ = lean_usize_dec_eq(v___x_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_inc(v_idx_3220_);
lean_inc(v_typeName_3219_);
lean_dec_ref(v___y_3196_);
v___x_3227_ = l_Lean_Expr_proj___override(v_typeName_3219_, v_idx_3220_, v_a_3223_);
v___x_3228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___x_3227_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; 
lean_dec(v_a_3223_);
v___x_3229_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3229_;
}
}
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v_post_3180_);
lean_dec_ref(v_pre_3178_);
return v___x_3222_;
}
}
default: 
{
lean_object* v___x_3230_; 
v___x_3230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3178_, v_post_3180_, v_usedLetOnly_3181_, v_skipConstInApp_3182_, v_skipInstances_3183_, v___y_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3230_;
}
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v_post_3180_);
lean_dec_ref(v_e_3179_);
lean_dec_ref(v_pre_3178_);
v_a_3240_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3190_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3190_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_3248_, lean_object* v_e_3249_, lean_object* v_post_3250_, lean_object* v_usedLetOnly_3251_, lean_object* v_skipConstInApp_3252_, lean_object* v_skipInstances_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v_usedLetOnly_boxed_3260_; uint8_t v_skipConstInApp_boxed_3261_; uint8_t v_skipInstances_boxed_3262_; lean_object* v_res_3263_; 
v_usedLetOnly_boxed_3260_ = lean_unbox(v_usedLetOnly_3251_);
v_skipConstInApp_boxed_3261_ = lean_unbox(v_skipConstInApp_3252_);
v_skipInstances_boxed_3262_ = lean_unbox(v_skipInstances_3253_);
v_res_3263_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v_pre_3248_, v_e_3249_, v_post_3250_, v_usedLetOnly_boxed_3260_, v_skipConstInApp_boxed_3261_, v_skipInstances_boxed_3262_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3264_, lean_object* v_post_3265_, uint8_t v_usedLetOnly_3266_, uint8_t v_skipConstInApp_3267_, uint8_t v_skipInstances_3268_, lean_object* v_e_3269_, lean_object* v_a_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_inc(v_a_3270_);
v___x_3276_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3276_, 0, lean_box(0));
lean_closure_set(v___x_3276_, 1, lean_box(0));
lean_closure_set(v___x_3276_, 2, v_a_3270_);
v___x_3277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3276_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3311_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3311_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3311_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3278_, v_e_3269_);
lean_dec(v_a_3278_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; 
lean_del_object(v___x_3280_);
v___x_3283_ = lean_box(v_usedLetOnly_3266_);
v___x_3284_ = lean_box(v_skipConstInApp_3267_);
v___x_3285_ = lean_box(v_skipInstances_3268_);
lean_inc_ref(v_e_3269_);
v___f_3286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3286_, 0, v_pre_3264_);
lean_closure_set(v___f_3286_, 1, v_e_3269_);
lean_closure_set(v___f_3286_, 2, v_post_3265_);
lean_closure_set(v___f_3286_, 3, v___x_3283_);
lean_closure_set(v___f_3286_, 4, v___x_3284_);
lean_closure_set(v___f_3286_, 5, v___x_3285_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
lean_inc(v_a_3270_);
v___x_3287_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3286_, v_a_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3287_);
lean_inc(v_a_3288_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3289_, 0, v_a_3270_);
lean_closure_set(v___f_3289_, 1, v_e_3269_);
lean_closure_set(v___f_3289_, 2, v_a_3288_);
v___x_3290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3289_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3298_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_a_3288_);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3288_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_a_3288_);
v_a_3299_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3290_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3290_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_e_3269_);
return v___x_3287_;
}
}
else
{
lean_object* v_val_3307_; lean_object* v___x_3309_; 
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_e_3269_);
lean_dec_ref(v_post_3265_);
lean_dec_ref(v_pre_3264_);
v_val_3307_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_val_3307_);
lean_dec_ref(v___x_3282_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v_val_3307_);
v___x_3309_ = v___x_3280_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_val_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_e_3269_);
lean_dec_ref(v_post_3265_);
lean_dec_ref(v_pre_3264_);
v_a_3312_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3277_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3277_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3320_, lean_object* v_pre_3321_, lean_object* v_post_3322_, lean_object* v_usedLetOnly_3323_, lean_object* v_skipConstInApp_3324_, lean_object* v_skipInstances_3325_, lean_object* v_body_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v_usedLetOnly_boxed_3334_; uint8_t v_skipConstInApp_boxed_3335_; uint8_t v_skipInstances_boxed_3336_; lean_object* v_res_3337_; 
v_usedLetOnly_boxed_3334_ = lean_unbox(v_usedLetOnly_3323_);
v_skipConstInApp_boxed_3335_ = lean_unbox(v_skipConstInApp_3324_);
v_skipInstances_boxed_3336_ = lean_unbox(v_skipInstances_3325_);
v_res_3337_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3320_, v_pre_3321_, v_post_3322_, v_usedLetOnly_boxed_3334_, v_skipConstInApp_boxed_3335_, v_skipInstances_boxed_3336_, v_body_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3338_, lean_object* v_post_3339_, uint8_t v_usedLetOnly_3340_, uint8_t v_skipConstInApp_3341_, uint8_t v_skipInstances_3342_, lean_object* v_fvars_3343_, lean_object* v_e_3344_, lean_object* v_a_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
if (lean_obj_tag(v_e_3344_) == 7)
{
lean_object* v_binderName_3351_; lean_object* v_binderType_3352_; lean_object* v_body_3353_; uint8_t v_binderInfo_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_binderName_3351_ = lean_ctor_get(v_e_3344_, 0);
lean_inc(v_binderName_3351_);
v_binderType_3352_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref(v_binderType_3352_);
v_body_3353_ = lean_ctor_get(v_e_3344_, 2);
lean_inc_ref(v_body_3353_);
v_binderInfo_3354_ = lean_ctor_get_uint8(v_e_3344_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3344_);
v___x_3355_ = lean_expr_instantiate_rev(v_binderType_3352_, v_fvars_3343_);
lean_dec_ref(v_binderType_3352_);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v_a_3345_);
lean_inc_ref(v_post_3339_);
lean_inc_ref(v_pre_3338_);
v___x_3356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v___x_3355_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
v___x_3358_ = lean_box(v_usedLetOnly_3340_);
v___x_3359_ = lean_box(v_skipConstInApp_3341_);
v___x_3360_ = lean_box(v_skipInstances_3342_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3361_, 0, v_fvars_3343_);
lean_closure_set(v___f_3361_, 1, v_pre_3338_);
lean_closure_set(v___f_3361_, 2, v_post_3339_);
lean_closure_set(v___f_3361_, 3, v___x_3358_);
lean_closure_set(v___f_3361_, 4, v___x_3359_);
lean_closure_set(v___f_3361_, 5, v___x_3360_);
lean_closure_set(v___f_3361_, 6, v_body_3353_);
v___x_3362_ = 0;
v___x_3363_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3351_, v_binderInfo_3354_, v_a_3357_, v___f_3361_, v___x_3362_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3363_;
}
else
{
lean_dec_ref(v_body_3353_);
lean_dec(v_binderName_3351_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_fvars_3343_);
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
return v___x_3356_;
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_expr_instantiate_rev(v_e_3344_, v_fvars_3343_);
lean_dec_ref(v_e_3344_);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v_a_3345_);
lean_inc_ref(v_post_3339_);
lean_inc_ref(v_pre_3338_);
v___x_3365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v___x_3364_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = 0;
v___x_3368_ = 1;
v___x_3369_ = 1;
v___x_3370_ = l_Lean_Meta_mkForallFVars(v_fvars_3343_, v_a_3366_, v___x_3367_, v_usedLetOnly_3340_, v___x_3368_, v___x_3369_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v_fvars_3343_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v_a_3371_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3372_;
}
else
{
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
return v___x_3370_;
}
}
else
{
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_fvars_3343_);
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
return v___x_3365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3373_, lean_object* v_pre_3374_, lean_object* v_post_3375_, uint8_t v_usedLetOnly_3376_, uint8_t v_skipConstInApp_3377_, uint8_t v_skipInstances_3378_, lean_object* v_body_3379_, lean_object* v_x_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_array_push(v_fvars_3373_, v_x_3380_);
v___x_3388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3374_, v_post_3375_, v_usedLetOnly_3376_, v_skipConstInApp_3377_, v_skipInstances_3378_, v___x_3387_, v_body_3379_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3389_, lean_object* v_post_3390_, lean_object* v_usedLetOnly_3391_, lean_object* v_skipConstInApp_3392_, lean_object* v_skipInstances_3393_, lean_object* v_e_3394_, lean_object* v_a_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v_usedLetOnly_boxed_3401_; uint8_t v_skipConstInApp_boxed_3402_; uint8_t v_skipInstances_boxed_3403_; lean_object* v_res_3404_; 
v_usedLetOnly_boxed_3401_ = lean_unbox(v_usedLetOnly_3391_);
v_skipConstInApp_boxed_3402_ = lean_unbox(v_skipConstInApp_3392_);
v_skipInstances_boxed_3403_ = lean_unbox(v_skipInstances_3393_);
v_res_3404_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3389_, v_post_3390_, v_usedLetOnly_boxed_3401_, v_skipConstInApp_boxed_3402_, v_skipInstances_boxed_3403_, v_e_3394_, v_a_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3405_, lean_object* v_post_3406_, lean_object* v_usedLetOnly_3407_, lean_object* v_skipConstInApp_3408_, lean_object* v_skipInstances_3409_, lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_bs_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v_usedLetOnly_boxed_3419_; uint8_t v_skipConstInApp_boxed_3420_; uint8_t v_skipInstances_boxed_3421_; size_t v_sz_boxed_3422_; size_t v_i_boxed_3423_; lean_object* v_res_3424_; 
v_usedLetOnly_boxed_3419_ = lean_unbox(v_usedLetOnly_3407_);
v_skipConstInApp_boxed_3420_ = lean_unbox(v_skipConstInApp_3408_);
v_skipInstances_boxed_3421_ = lean_unbox(v_skipInstances_3409_);
v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3423_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3405_, v_post_3406_, v_usedLetOnly_boxed_3419_, v_skipConstInApp_boxed_3420_, v_skipInstances_boxed_3421_, v_sz_boxed_3422_, v_i_boxed_3423_, v_bs_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3425_, lean_object* v_post_3426_, lean_object* v_usedLetOnly_3427_, lean_object* v_skipConstInApp_3428_, lean_object* v_skipInstances_3429_, lean_object* v_e_3430_, lean_object* v_a_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v_usedLetOnly_boxed_3437_; uint8_t v_skipConstInApp_boxed_3438_; uint8_t v_skipInstances_boxed_3439_; lean_object* v_res_3440_; 
v_usedLetOnly_boxed_3437_ = lean_unbox(v_usedLetOnly_3427_);
v_skipConstInApp_boxed_3438_ = lean_unbox(v_skipConstInApp_3428_);
v_skipInstances_boxed_3439_ = lean_unbox(v_skipInstances_3429_);
v_res_3440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3425_, v_post_3426_, v_usedLetOnly_boxed_3437_, v_skipConstInApp_boxed_3438_, v_skipInstances_boxed_3439_, v_e_3430_, v_a_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3441_, lean_object* v_post_3442_, lean_object* v_usedLetOnly_3443_, lean_object* v_skipConstInApp_3444_, lean_object* v_skipInstances_3445_, lean_object* v_fvars_3446_, lean_object* v_e_3447_, lean_object* v_a_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
uint8_t v_usedLetOnly_boxed_3454_; uint8_t v_skipConstInApp_boxed_3455_; uint8_t v_skipInstances_boxed_3456_; lean_object* v_res_3457_; 
v_usedLetOnly_boxed_3454_ = lean_unbox(v_usedLetOnly_3443_);
v_skipConstInApp_boxed_3455_ = lean_unbox(v_skipConstInApp_3444_);
v_skipInstances_boxed_3456_ = lean_unbox(v_skipInstances_3445_);
v_res_3457_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3441_, v_post_3442_, v_usedLetOnly_boxed_3454_, v_skipConstInApp_boxed_3455_, v_skipInstances_boxed_3456_, v_fvars_3446_, v_e_3447_, v_a_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3458_, lean_object* v_post_3459_, lean_object* v_usedLetOnly_3460_, lean_object* v_skipConstInApp_3461_, lean_object* v_skipInstances_3462_, lean_object* v_fvars_3463_, lean_object* v_e_3464_, lean_object* v_a_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v_usedLetOnly_boxed_3471_; uint8_t v_skipConstInApp_boxed_3472_; uint8_t v_skipInstances_boxed_3473_; lean_object* v_res_3474_; 
v_usedLetOnly_boxed_3471_ = lean_unbox(v_usedLetOnly_3460_);
v_skipConstInApp_boxed_3472_ = lean_unbox(v_skipConstInApp_3461_);
v_skipInstances_boxed_3473_ = lean_unbox(v_skipInstances_3462_);
v_res_3474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3458_, v_post_3459_, v_usedLetOnly_boxed_3471_, v_skipConstInApp_boxed_3472_, v_skipInstances_boxed_3473_, v_fvars_3463_, v_e_3464_, v_a_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3475_, lean_object* v_post_3476_, lean_object* v_usedLetOnly_3477_, lean_object* v_skipConstInApp_3478_, lean_object* v_skipInstances_3479_, lean_object* v_fvars_3480_, lean_object* v_e_3481_, lean_object* v_a_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
uint8_t v_usedLetOnly_boxed_3488_; uint8_t v_skipConstInApp_boxed_3489_; uint8_t v_skipInstances_boxed_3490_; lean_object* v_res_3491_; 
v_usedLetOnly_boxed_3488_ = lean_unbox(v_usedLetOnly_3477_);
v_skipConstInApp_boxed_3489_ = lean_unbox(v_skipConstInApp_3478_);
v_skipInstances_boxed_3490_ = lean_unbox(v_skipInstances_3479_);
v_res_3491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3475_, v_post_3476_, v_usedLetOnly_boxed_3488_, v_skipConstInApp_boxed_3489_, v_skipInstances_boxed_3490_, v_fvars_3480_, v_e_3481_, v_a_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3492_, lean_object* v___x_3493_, lean_object* v_pre_3494_, lean_object* v_post_3495_, lean_object* v_usedLetOnly_3496_, lean_object* v_skipConstInApp_3497_, lean_object* v_skipInstances_3498_, lean_object* v_a_3499_, lean_object* v_b_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v_usedLetOnly_boxed_3507_; uint8_t v_skipConstInApp_boxed_3508_; uint8_t v_skipInstances_boxed_3509_; lean_object* v_res_3510_; 
v_usedLetOnly_boxed_3507_ = lean_unbox(v_usedLetOnly_3496_);
v_skipConstInApp_boxed_3508_ = lean_unbox(v_skipConstInApp_3497_);
v_skipInstances_boxed_3509_ = lean_unbox(v_skipInstances_3498_);
v_res_3510_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3492_, v___x_3493_, v_pre_3494_, v_post_3495_, v_usedLetOnly_boxed_3507_, v_skipConstInApp_boxed_3508_, v_skipInstances_boxed_3509_, v_a_3499_, v_b_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec_ref(v___x_3493_);
lean_dec(v_upperBound_3492_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3511_, lean_object* v_pre_3512_, lean_object* v_post_3513_, lean_object* v_usedLetOnly_3514_, lean_object* v_skipConstInApp_3515_, lean_object* v_x_3516_, lean_object* v_x_3517_, lean_object* v_x_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
uint8_t v_skipInstances_boxed_3525_; uint8_t v_usedLetOnly_boxed_3526_; uint8_t v_skipConstInApp_boxed_3527_; lean_object* v_res_3528_; 
v_skipInstances_boxed_3525_ = lean_unbox(v_skipInstances_3511_);
v_usedLetOnly_boxed_3526_ = lean_unbox(v_usedLetOnly_3514_);
v_skipConstInApp_boxed_3527_ = lean_unbox(v_skipConstInApp_3515_);
v_res_3528_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3525_, v_pre_3512_, v_post_3513_, v_usedLetOnly_boxed_3526_, v_skipConstInApp_boxed_3527_, v_x_3516_, v_x_3517_, v_x_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_unsigned_to_nat(16u);
v___x_3531_ = lean_mk_array(v___x_3530_, v___x_3529_);
return v___x_3531_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3533_ = lean_unsigned_to_nat(0u);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3536_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3536_, 0, lean_box(0));
lean_closure_set(v___x_3536_, 1, lean_box(0));
lean_closure_set(v___x_3536_, 2, v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3537_, lean_object* v_pre_3538_, lean_object* v_post_3539_, uint8_t v_usedLetOnly_3540_, uint8_t v_skipConstInApp_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_a_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; 
v___x_3547_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3548_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3547_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v___x_3548_);
v___x_3550_ = 0;
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v_a_3549_);
v___x_3551_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3538_, v_post_3539_, v_usedLetOnly_3540_, v_skipConstInApp_3541_, v___x_3550_, v_input_3537_, v_a_3549_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref(v___x_3551_);
v___x_3553_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3553_, 0, lean_box(0));
lean_closure_set(v___x_3553_, 1, lean_box(0));
lean_closure_set(v___x_3553_, 2, v_a_3549_);
v___x_3554_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3553_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v___x_3554_, 0);
lean_dec(v_unused_3562_);
v___x_3556_ = v___x_3554_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_dec(v___x_3554_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v_a_3552_);
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3552_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
else
{
lean_dec(v_a_3549_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v___x_3551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3563_, lean_object* v_pre_3564_, lean_object* v_post_3565_, lean_object* v_usedLetOnly_3566_, lean_object* v_skipConstInApp_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v_usedLetOnly_boxed_3573_; uint8_t v_skipConstInApp_boxed_3574_; lean_object* v_res_3575_; 
v_usedLetOnly_boxed_3573_ = lean_unbox(v_usedLetOnly_3566_);
v_skipConstInApp_boxed_3574_ = lean_unbox(v_skipConstInApp_3567_);
v_res_3575_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3563_, v_pre_3564_, v_post_3565_, v_usedLetOnly_boxed_3573_, v_skipConstInApp_boxed_3574_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3577_, lean_object* v_p_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___x_3584_; lean_object* v_a_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; 
v___x_3584_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3577_, v_a_3580_);
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref(v___x_3584_);
v___f_3586_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3587_, 0, v_p_3578_);
v___x_3588_ = 0;
v___x_3589_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3585_, v___f_3586_, v___f_3587_, v___x_3588_, v___x_3588_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3590_, lean_object* v_p_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Meta_etaStructReduce(v_e_3590_, v_p_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3598_, lean_object* v___x_3599_, lean_object* v_pre_3600_, lean_object* v_post_3601_, uint8_t v_usedLetOnly_3602_, uint8_t v_skipConstInApp_3603_, uint8_t v_skipInstances_3604_, lean_object* v___x_3605_, lean_object* v_inst_3606_, lean_object* v_R_3607_, lean_object* v_a_3608_, lean_object* v_b_3609_, lean_object* v_c_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3598_, v___x_3599_, v_pre_3600_, v_post_3601_, v_usedLetOnly_3602_, v_skipConstInApp_3603_, v_skipInstances_3604_, v_a_3608_, v_b_3609_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3618_ = _args[0];
lean_object* v___x_3619_ = _args[1];
lean_object* v_pre_3620_ = _args[2];
lean_object* v_post_3621_ = _args[3];
lean_object* v_usedLetOnly_3622_ = _args[4];
lean_object* v_skipConstInApp_3623_ = _args[5];
lean_object* v_skipInstances_3624_ = _args[6];
lean_object* v___x_3625_ = _args[7];
lean_object* v_inst_3626_ = _args[8];
lean_object* v_R_3627_ = _args[9];
lean_object* v_a_3628_ = _args[10];
lean_object* v_b_3629_ = _args[11];
lean_object* v_c_3630_ = _args[12];
lean_object* v___y_3631_ = _args[13];
lean_object* v___y_3632_ = _args[14];
lean_object* v___y_3633_ = _args[15];
lean_object* v___y_3634_ = _args[16];
lean_object* v___y_3635_ = _args[17];
lean_object* v___y_3636_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3637_; uint8_t v_skipConstInApp_boxed_3638_; uint8_t v_skipInstances_boxed_3639_; lean_object* v_res_3640_; 
v_usedLetOnly_boxed_3637_ = lean_unbox(v_usedLetOnly_3622_);
v_skipConstInApp_boxed_3638_ = lean_unbox(v_skipConstInApp_3623_);
v_skipInstances_boxed_3639_ = lean_unbox(v_skipInstances_3624_);
v_res_3640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3618_, v___x_3619_, v_pre_3620_, v_post_3621_, v_usedLetOnly_boxed_3637_, v_skipConstInApp_boxed_3638_, v_skipInstances_boxed_3639_, v___x_3625_, v_inst_3626_, v_R_3627_, v_a_3628_, v_b_3629_, v_c_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___x_3625_);
lean_dec_ref(v___x_3619_);
lean_dec(v_upperBound_3618_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3641_, lean_object* v_m_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3642_, v_a_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3645_, lean_object* v_m_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3645_, v_m_3646_, v_a_3647_);
lean_dec_ref(v_a_3647_);
lean_dec_ref(v_m_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3649_, lean_object* v_name_3650_, uint8_t v_bi_3651_, lean_object* v_type_3652_, lean_object* v_k_3653_, uint8_t v_kind_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3650_, v_bi_3651_, v_type_3652_, v_k_3653_, v_kind_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3662_, lean_object* v_name_3663_, lean_object* v_bi_3664_, lean_object* v_type_3665_, lean_object* v_k_3666_, lean_object* v_kind_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v_bi_boxed_3674_; uint8_t v_kind_boxed_3675_; lean_object* v_res_3676_; 
v_bi_boxed_3674_ = lean_unbox(v_bi_3664_);
v_kind_boxed_3675_ = lean_unbox(v_kind_3667_);
v_res_3676_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3662_, v_name_3663_, v_bi_boxed_3674_, v_type_3665_, v_k_3666_, v_kind_boxed_3675_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3677_, lean_object* v_name_3678_, lean_object* v_type_3679_, lean_object* v_val_3680_, lean_object* v_k_3681_, uint8_t v_nondep_3682_, uint8_t v_kind_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3678_, v_type_3679_, v_val_3680_, v_k_3681_, v_nondep_3682_, v_kind_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3691_, lean_object* v_name_3692_, lean_object* v_type_3693_, lean_object* v_val_3694_, lean_object* v_k_3695_, lean_object* v_nondep_3696_, lean_object* v_kind_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v_nondep_boxed_3704_; uint8_t v_kind_boxed_3705_; lean_object* v_res_3706_; 
v_nondep_boxed_3704_ = lean_unbox(v_nondep_3696_);
v_kind_boxed_3705_ = lean_unbox(v_kind_3697_);
v_res_3706_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3691_, v_name_3692_, v_type_3693_, v_val_3694_, v_k_3695_, v_nondep_boxed_3704_, v_kind_boxed_3705_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3707_, lean_object* v_ref_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3708_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_ref_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3715_, v_ref_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3723_, lean_object* v_x_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3732_, lean_object* v_x_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3732_, v_x_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3741_, lean_object* v_m_3742_, lean_object* v_a_3743_, lean_object* v_b_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3742_, v_a_3743_, v_b_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3746_, lean_object* v_a_3747_, lean_object* v_x_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3747_, v_x_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3750_, lean_object* v_a_3751_, lean_object* v_x_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3750_, v_a_3751_, v_x_3752_);
lean_dec(v_x_3752_);
lean_dec_ref(v_a_3751_);
return v_res_3753_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3754_, lean_object* v_a_3755_, lean_object* v_x_3756_){
_start:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3755_, v_x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3758_, lean_object* v_a_3759_, lean_object* v_x_3760_){
_start:
{
uint8_t v_res_3761_; lean_object* v_r_3762_; 
v_res_3761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3758_, v_a_3759_, v_x_3760_);
lean_dec(v_x_3760_);
lean_dec_ref(v_a_3759_);
v_r_3762_ = lean_box(v_res_3761_);
return v_r_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3763_, lean_object* v_data_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3766_, lean_object* v_a_3767_, lean_object* v_b_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3767_, v_b_3768_, v_x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3771_, lean_object* v_i_3772_, lean_object* v_source_3773_, lean_object* v_target_3774_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3772_, v_source_3773_, v_target_3774_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3777_, v_x_3778_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3780_, lean_object* v_inst_3781_, lean_object* v_toBind_3782_, lean_object* v___f_3783_, lean_object* v_____do__lift_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3785_, 0, v_____do__lift_3784_);
lean_closure_set(v___x_3785_, 1, v_binderType_3780_);
v___x_3786_ = lean_apply_2(v_inst_3781_, lean_box(0), v___x_3785_);
v___x_3787_ = lean_apply_4(v_toBind_3782_, lean_box(0), lean_box(0), v___x_3786_, v___f_3783_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3788_, lean_object* v_usedFields_3789_, lean_object* v_binderName_3790_, lean_object* v_body_3791_, lean_object* v_val_3792_, lean_object* v_inst_3793_, lean_object* v_inst_3794_, lean_object* v_fieldVal_x3f_3795_, lean_object* v_____do__lift_3796_){
_start:
{
uint8_t v_____do__lift_469__boxed_3797_; lean_object* v_res_3798_; 
v_____do__lift_469__boxed_3797_ = lean_unbox(v_____do__lift_3796_);
v_res_3798_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3788_, v_usedFields_3789_, v_binderName_3790_, v_body_3791_, v_val_3792_, v_inst_3793_, v_inst_3794_, v_fieldVal_x3f_3795_, v_____do__lift_469__boxed_3797_);
lean_dec_ref(v_val_3792_);
lean_dec_ref(v_body_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3799_, lean_object* v_usedFields_3800_, lean_object* v_binderName_3801_, lean_object* v_body_3802_, lean_object* v_inst_3803_, lean_object* v_inst_3804_, lean_object* v_fieldVal_x3f_3805_, lean_object* v_binderType_3806_, lean_object* v_toBind_3807_, lean_object* v_____x_3808_){
_start:
{
if (lean_obj_tag(v_____x_3808_) == 1)
{
lean_object* v_val_3809_; lean_object* v___f_3810_; lean_object* v___f_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_val_3809_ = lean_ctor_get(v_____x_3808_, 0);
lean_inc(v_val_3809_);
lean_dec_ref(v_____x_3808_);
lean_inc(v_inst_3804_);
lean_inc(v_val_3809_);
v___f_3810_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3810_, 0, v_toPure_3799_);
lean_closure_set(v___f_3810_, 1, v_usedFields_3800_);
lean_closure_set(v___f_3810_, 2, v_binderName_3801_);
lean_closure_set(v___f_3810_, 3, v_body_3802_);
lean_closure_set(v___f_3810_, 4, v_val_3809_);
lean_closure_set(v___f_3810_, 5, v_inst_3803_);
lean_closure_set(v___f_3810_, 6, v_inst_3804_);
lean_closure_set(v___f_3810_, 7, v_fieldVal_x3f_3805_);
lean_inc(v_toBind_3807_);
lean_inc(v_inst_3804_);
v___f_3811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3811_, 0, v_binderType_3806_);
lean_closure_set(v___f_3811_, 1, v_inst_3804_);
lean_closure_set(v___f_3811_, 2, v_toBind_3807_);
lean_closure_set(v___f_3811_, 3, v___f_3810_);
v___x_3812_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3812_, 0, v_val_3809_);
v___x_3813_ = lean_apply_2(v_inst_3804_, lean_box(0), v___x_3812_);
v___x_3814_ = lean_apply_4(v_toBind_3807_, lean_box(0), lean_box(0), v___x_3813_, v___f_3811_);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v_____x_3808_);
lean_dec(v_toBind_3807_);
lean_dec_ref(v_binderType_3806_);
lean_dec(v_fieldVal_x3f_3805_);
lean_dec(v_inst_3804_);
lean_dec_ref(v_inst_3803_);
lean_dec_ref(v_body_3802_);
lean_dec(v_binderName_3801_);
lean_dec(v_usedFields_3800_);
v___x_3815_ = lean_box(0);
v___x_3816_ = lean_apply_2(v_toPure_3799_, lean_box(0), v___x_3815_);
return v___x_3816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3820_, lean_object* v_inst_3821_, lean_object* v_fieldVal_x3f_3822_, lean_object* v_usedFields_3823_, lean_object* v_e_3824_){
_start:
{
lean_object* v_toApplicative_3825_; lean_object* v_toBind_3826_; lean_object* v_toPure_3827_; 
v_toApplicative_3825_ = lean_ctor_get(v_inst_3820_, 0);
v_toBind_3826_ = lean_ctor_get(v_inst_3820_, 1);
v_toPure_3827_ = lean_ctor_get(v_toApplicative_3825_, 1);
lean_inc(v_toPure_3827_);
if (lean_obj_tag(v_e_3824_) == 6)
{
lean_object* v_binderName_3832_; lean_object* v_binderType_3833_; lean_object* v_body_3834_; lean_object* v___f_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_inc(v_toBind_3826_);
v_binderName_3832_ = lean_ctor_get(v_e_3824_, 0);
lean_inc(v_binderName_3832_);
v_binderType_3833_ = lean_ctor_get(v_e_3824_, 1);
lean_inc_ref(v_binderType_3833_);
v_body_3834_ = lean_ctor_get(v_e_3824_, 2);
lean_inc_ref(v_body_3834_);
lean_dec_ref(v_e_3824_);
lean_inc(v_toBind_3826_);
lean_inc(v_fieldVal_x3f_3822_);
lean_inc(v_binderName_3832_);
v___f_3835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3835_, 0, v_toPure_3827_);
lean_closure_set(v___f_3835_, 1, v_usedFields_3823_);
lean_closure_set(v___f_3835_, 2, v_binderName_3832_);
lean_closure_set(v___f_3835_, 3, v_body_3834_);
lean_closure_set(v___f_3835_, 4, v_inst_3820_);
lean_closure_set(v___f_3835_, 5, v_inst_3821_);
lean_closure_set(v___f_3835_, 6, v_fieldVal_x3f_3822_);
lean_closure_set(v___f_3835_, 7, v_binderType_3833_);
lean_closure_set(v___f_3835_, 8, v_toBind_3826_);
v___x_3836_ = lean_apply_1(v_fieldVal_x3f_3822_, v_binderName_3832_);
v___x_3837_ = lean_apply_4(v_toBind_3826_, lean_box(0), lean_box(0), v___x_3836_, v___f_3835_);
return v___x_3837_;
}
else
{
lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_fieldVal_x3f_3822_);
lean_dec(v_inst_3821_);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_inst_3820_);
if (v_isSharedCheck_3854_ == 0)
{
lean_object* v_unused_3855_; lean_object* v_unused_3856_; 
v_unused_3855_ = lean_ctor_get(v_inst_3820_, 1);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_inst_3820_, 0);
lean_dec(v_unused_3856_);
v___x_3839_ = v_inst_3820_;
v_isShared_3840_ = v_isSharedCheck_3854_;
goto v_resetjp_3838_;
}
else
{
lean_dec(v_inst_3820_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3854_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; uint8_t v___x_3842_; 
lean_inc_ref(v_e_3824_);
v___x_3841_ = l_Lean_Expr_cleanupAnnotations(v_e_3824_);
v___x_3842_ = l_Lean_Expr_isApp(v___x_3841_);
if (v___x_3842_ == 0)
{
lean_dec_ref(v___x_3841_);
lean_del_object(v___x_3839_);
goto v___jp_3828_;
}
else
{
lean_object* v_arg_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v_arg_3843_ = lean_ctor_get(v___x_3841_, 1);
lean_inc_ref(v_arg_3843_);
v___x_3844_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3841_);
v___x_3845_ = l_Lean_Expr_isApp(v___x_3844_);
if (v___x_3845_ == 0)
{
lean_dec_ref(v___x_3844_);
lean_dec_ref(v_arg_3843_);
lean_del_object(v___x_3839_);
goto v___jp_3828_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3844_);
v___x_3847_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3848_ = l_Lean_Expr_isConstOf(v___x_3846_, v___x_3847_);
lean_dec_ref(v___x_3846_);
if (v___x_3848_ == 0)
{
lean_dec_ref(v_arg_3843_);
lean_del_object(v___x_3839_);
goto v___jp_3828_;
}
else
{
lean_object* v___x_3850_; 
lean_dec_ref(v_e_3824_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 1, v_arg_3843_);
lean_ctor_set(v___x_3839_, 0, v_usedFields_3823_);
v___x_3850_ = v___x_3839_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_usedFields_3823_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_arg_3843_);
v___x_3850_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
v___x_3852_ = lean_apply_2(v_toPure_3827_, lean_box(0), v___x_3851_);
return v___x_3852_;
}
}
}
}
}
}
v___jp_3828_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_usedFields_3823_);
lean_ctor_set(v___x_3829_, 1, v_e_3824_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
v___x_3831_ = lean_apply_2(v_toPure_3827_, lean_box(0), v___x_3830_);
return v___x_3831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3857_, lean_object* v_usedFields_3858_, lean_object* v_binderName_3859_, lean_object* v_body_3860_, lean_object* v_val_3861_, lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_fieldVal_x3f_3864_, uint8_t v_____do__lift_3865_){
_start:
{
if (v_____do__lift_3865_ == 0)
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec(v_fieldVal_x3f_3864_);
lean_dec(v_inst_3863_);
lean_dec_ref(v_inst_3862_);
lean_dec(v_binderName_3859_);
lean_dec(v_usedFields_3858_);
v___x_3866_ = lean_box(0);
v___x_3867_ = lean_apply_2(v_toPure_3857_, lean_box(0), v___x_3866_);
return v___x_3867_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_dec(v_toPure_3857_);
v___x_3868_ = l_Lean_NameSet_insert(v_usedFields_3858_, v_binderName_3859_);
v___x_3869_ = lean_expr_instantiate1(v_body_3860_, v_val_3861_);
v___x_3870_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3862_, v_inst_3863_, v_fieldVal_x3f_3864_, v___x_3868_, v___x_3869_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3871_, lean_object* v_inst_3872_, lean_object* v_inst_3873_, lean_object* v_fieldVal_x3f_3874_, lean_object* v_usedFields_3875_, lean_object* v_e_3876_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3872_, v_inst_3873_, v_fieldVal_x3f_3874_, v_usedFields_3875_, v_e_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3878_, lean_object* v_inst_3879_, lean_object* v_fieldVal_x3f_3880_, lean_object* v_toPure_3881_, lean_object* v_____s_3882_){
_start:
{
lean_object* v_fst_3883_; 
v_fst_3883_ = lean_ctor_get(v_____s_3882_, 0);
if (lean_obj_tag(v_fst_3883_) == 0)
{
lean_object* v_snd_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec(v_toPure_3881_);
v_snd_3884_ = lean_ctor_get(v_____s_3882_, 1);
lean_inc(v_snd_3884_);
lean_dec_ref(v_____s_3882_);
v___x_3885_ = l_Lean_NameSet_empty;
v___x_3886_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3878_, v_inst_3879_, v_fieldVal_x3f_3880_, v___x_3885_, v_snd_3884_);
return v___x_3886_;
}
else
{
lean_object* v_val_3887_; lean_object* v___x_3888_; 
lean_inc_ref(v_fst_3883_);
lean_dec_ref(v_____s_3882_);
lean_dec(v_fieldVal_x3f_3880_);
lean_dec(v_inst_3879_);
lean_dec_ref(v_inst_3878_);
v_val_3887_ = lean_ctor_get(v_fst_3883_, 0);
lean_inc(v_val_3887_);
lean_dec_ref(v_fst_3883_);
v___x_3888_ = lean_apply_2(v_toPure_3881_, lean_box(0), v_val_3887_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_cinfo_3889_, lean_object* v_us_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3889_, v_us_3890_, v___y_3893_, v___y_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_cinfo_3897_, lean_object* v_us_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_cinfo_3897_, v_us_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec_ref(v_cinfo_3897_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_body_3905_, lean_object* v_a_3906_, lean_object* v___x_3907_, lean_object* v_toPure_3908_, lean_object* v_____r_3909_){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3910_ = lean_expr_instantiate1(v_body_3905_, v_a_3906_);
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3907_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___x_3913_ = lean_apply_2(v_toPure_3908_, lean_box(0), v___x_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_body_3914_, lean_object* v_a_3915_, lean_object* v___x_3916_, lean_object* v_toPure_3917_, lean_object* v_____r_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_body_3914_, v_a_3915_, v___x_3916_, v_toPure_3917_, v_____r_3918_);
lean_dec_ref(v_a_3915_);
lean_dec_ref(v_body_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_snd_3922_, lean_object* v_toPure_3923_, lean_object* v___f_3924_, uint8_t v_____do__lift_3925_){
_start:
{
if (v_____do__lift_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec(v___f_3924_);
v___x_3926_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___closed__0));
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v_snd_3922_);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
v___x_3929_ = lean_apply_2(v_toPure_3923_, lean_box(0), v___x_3928_);
return v___x_3929_;
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_dec(v_toPure_3923_);
lean_dec(v_snd_3922_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_apply_1(v___f_3924_, v___x_3930_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___boxed(lean_object* v_snd_3932_, lean_object* v_toPure_3933_, lean_object* v___f_3934_, lean_object* v_____do__lift_3935_){
_start:
{
uint8_t v_____do__lift_862__boxed_3936_; lean_object* v_res_3937_; 
v_____do__lift_862__boxed_3936_ = lean_unbox(v_____do__lift_3935_);
v_res_3937_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(v_snd_3932_, v_toPure_3933_, v___f_3934_, v_____do__lift_862__boxed_3936_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v_binderType_3938_, lean_object* v_inst_3939_, lean_object* v_toBind_3940_, lean_object* v___f_3941_, lean_object* v_____do__lift_3942_){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3943_, 0, v_____do__lift_3942_);
lean_closure_set(v___x_3943_, 1, v_binderType_3938_);
v___x_3944_ = lean_apply_2(v_inst_3939_, lean_box(0), v___x_3943_);
v___x_3945_ = lean_apply_4(v_toBind_3940_, lean_box(0), lean_box(0), v___x_3944_, v___f_3941_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v___x_3946_, lean_object* v_toPure_3947_, lean_object* v_levels_x3f_3948_, uint8_t v___x_3949_, lean_object* v_inst_3950_, lean_object* v_toBind_3951_, lean_object* v_a_3952_, lean_object* v_x_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_snd_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3976_; 
v_snd_3955_ = lean_ctor_get(v___y_3954_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___y_3954_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; 
v_unused_3977_ = lean_ctor_get(v___y_3954_, 0);
lean_dec(v_unused_3977_);
v___x_3957_ = v___y_3954_;
v_isShared_3958_ = v_isSharedCheck_3976_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_snd_3955_);
lean_dec(v___y_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3976_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
if (lean_obj_tag(v_snd_3955_) == 6)
{
lean_object* v_binderType_3959_; lean_object* v_body_3960_; lean_object* v___f_3961_; 
lean_del_object(v___x_3957_);
v_binderType_3959_ = lean_ctor_get(v_snd_3955_, 1);
lean_inc_ref(v_binderType_3959_);
v_body_3960_ = lean_ctor_get(v_snd_3955_, 2);
lean_inc(v_toPure_3947_);
lean_inc(v___x_3946_);
lean_inc_ref(v_a_3952_);
lean_inc_ref(v_body_3960_);
v___f_3961_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_3961_, 0, v_body_3960_);
lean_closure_set(v___f_3961_, 1, v_a_3952_);
lean_closure_set(v___f_3961_, 2, v___x_3946_);
lean_closure_set(v___f_3961_, 3, v_toPure_3947_);
if (lean_obj_tag(v_levels_x3f_3948_) == 0)
{
if (v___x_3949_ == 0)
{
lean_inc_ref(v_body_3960_);
lean_dec_ref(v___f_3961_);
lean_dec_ref(v_binderType_3959_);
lean_dec_ref(v_snd_3955_);
lean_dec(v_toBind_3951_);
lean_dec(v_inst_3950_);
goto v___jp_3962_;
}
else
{
lean_object* v___f_3965_; lean_object* v___f_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec(v___x_3946_);
v___f_3965_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_3965_, 0, v_snd_3955_);
lean_closure_set(v___f_3965_, 1, v_toPure_3947_);
lean_closure_set(v___f_3965_, 2, v___f_3961_);
lean_inc(v_toBind_3951_);
lean_inc(v_inst_3950_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3966_, 0, v_binderType_3959_);
lean_closure_set(v___f_3966_, 1, v_inst_3950_);
lean_closure_set(v___f_3966_, 2, v_toBind_3951_);
lean_closure_set(v___f_3966_, 3, v___f_3965_);
v___x_3967_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3967_, 0, v_a_3952_);
v___x_3968_ = lean_apply_2(v_inst_3950_, lean_box(0), v___x_3967_);
v___x_3969_ = lean_apply_4(v_toBind_3951_, lean_box(0), lean_box(0), v___x_3968_, v___f_3966_);
return v___x_3969_;
}
}
else
{
lean_inc_ref(v_body_3960_);
lean_dec_ref(v___f_3961_);
lean_dec_ref(v_binderType_3959_);
lean_dec_ref(v_snd_3955_);
lean_dec(v_toBind_3951_);
lean_dec(v_inst_3950_);
goto v___jp_3962_;
}
v___jp_3962_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_box(0);
v___x_3964_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_body_3960_, v_a_3952_, v___x_3946_, v_toPure_3947_, v___x_3963_);
lean_dec_ref(v_a_3952_);
lean_dec_ref(v_body_3960_);
return v___x_3964_;
}
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
lean_dec_ref(v_a_3952_);
lean_dec(v_toBind_3951_);
lean_dec(v_inst_3950_);
lean_dec(v___x_3946_);
v___x_3970_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3___closed__0));
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3970_);
v___x_3972_ = v___x_3957_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_snd_3955_);
v___x_3972_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = lean_apply_2(v_toPure_3947_, lean_box(0), v___x_3973_);
return v___x_3974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v___x_3978_, lean_object* v_toPure_3979_, lean_object* v_levels_x3f_3980_, lean_object* v___x_3981_, lean_object* v_inst_3982_, lean_object* v_toBind_3983_, lean_object* v_a_3984_, lean_object* v_x_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___x_898__boxed_3987_; lean_object* v_res_3988_; 
v___x_898__boxed_3987_ = lean_unbox(v___x_3981_);
v_res_3988_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v___x_3978_, v_toPure_3979_, v_levels_x3f_3980_, v___x_898__boxed_3987_, v_inst_3982_, v_toBind_3983_, v_a_3984_, v_x_3985_, v___y_3986_);
lean_dec(v_levels_x3f_3980_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_toPure_3989_, lean_object* v_levels_x3f_3990_, uint8_t v___x_3991_, lean_object* v_inst_3992_, lean_object* v_toBind_3993_, lean_object* v_params_3994_, lean_object* v_inst_3995_, lean_object* v___f_3996_, lean_object* v_val_3997_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___f_4000_; lean_object* v___x_4001_; size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_box(v___x_3991_);
lean_inc(v_toBind_3993_);
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 6);
lean_closure_set(v___f_4000_, 0, v___x_3998_);
lean_closure_set(v___f_4000_, 1, v_toPure_3989_);
lean_closure_set(v___f_4000_, 2, v_levels_x3f_3990_);
lean_closure_set(v___f_4000_, 3, v___x_3999_);
lean_closure_set(v___f_4000_, 4, v_inst_3992_);
lean_closure_set(v___f_4000_, 5, v_toBind_3993_);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3998_);
lean_ctor_set(v___x_4001_, 1, v_val_3997_);
v_sz_4002_ = lean_array_size(v_params_3994_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3995_, v_params_3994_, v___f_4000_, v_sz_4002_, v___x_4003_, v___x_4001_);
v___x_4005_ = lean_apply_4(v_toBind_3993_, lean_box(0), lean_box(0), v___x_4004_, v___f_3996_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_toPure_4006_, lean_object* v_levels_x3f_4007_, lean_object* v___x_4008_, lean_object* v_inst_4009_, lean_object* v_toBind_4010_, lean_object* v_params_4011_, lean_object* v_inst_4012_, lean_object* v___f_4013_, lean_object* v_val_4014_){
_start:
{
uint8_t v___x_960__boxed_4015_; lean_object* v_res_4016_; 
v___x_960__boxed_4015_ = lean_unbox(v___x_4008_);
v_res_4016_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_toPure_4006_, v_levels_x3f_4007_, v___x_960__boxed_4015_, v_inst_4009_, v_toBind_4010_, v_params_4011_, v_inst_4012_, v___f_4013_, v_val_4014_);
return v_res_4016_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4020_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4021_ = lean_unsigned_to_nat(2u);
v___x_4022_ = lean_unsigned_to_nat(202u);
v___x_4023_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4024_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4025_ = l_mkPanicMessageWithDecl(v___x_4024_, v___x_4023_, v___x_4022_, v___x_4021_, v___x_4020_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4026_, lean_object* v_inst_4027_, lean_object* v_toPure_4028_, lean_object* v_levels_x3f_4029_, lean_object* v_inst_4030_, lean_object* v_toBind_4031_, lean_object* v_params_4032_, lean_object* v___f_4033_, lean_object* v_us_4034_){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_4035_ = l_List_lengthTR___redArg(v_us_4034_);
v___x_4036_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4026_);
v___x_4037_ = l_List_lengthTR___redArg(v___x_4036_);
lean_dec(v___x_4036_);
v___x_4038_ = lean_nat_dec_eq(v___x_4035_, v___x_4037_);
lean_dec(v___x_4037_);
lean_dec(v___x_4035_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec(v_us_4034_);
lean_dec(v___f_4033_);
lean_dec_ref(v_params_4032_);
lean_dec(v_toBind_4031_);
lean_dec(v_inst_4030_);
lean_dec(v_levels_x3f_4029_);
lean_dec(v_toPure_4028_);
lean_dec_ref(v_cinfo_4026_);
v___x_4039_ = lean_box(0);
v___x_4040_ = l_instInhabitedOfMonad___redArg(v_inst_4027_, v___x_4039_);
v___x_4041_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4042_ = l_panic___redArg(v___x_4040_, v___x_4041_);
return v___x_4042_;
}
else
{
lean_object* v___f_4043_; lean_object* v___x_4044_; lean_object* v___f_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 7, 2);
lean_closure_set(v___f_4043_, 0, v_cinfo_4026_);
lean_closure_set(v___f_4043_, 1, v_us_4034_);
v___x_4044_ = lean_box(v___x_4038_);
lean_inc(v_toBind_4031_);
lean_inc(v_inst_4030_);
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 9, 8);
lean_closure_set(v___f_4045_, 0, v_toPure_4028_);
lean_closure_set(v___f_4045_, 1, v_levels_x3f_4029_);
lean_closure_set(v___f_4045_, 2, v___x_4044_);
lean_closure_set(v___f_4045_, 3, v_inst_4030_);
lean_closure_set(v___f_4045_, 4, v_toBind_4031_);
lean_closure_set(v___f_4045_, 5, v_params_4032_);
lean_closure_set(v___f_4045_, 6, v_inst_4027_);
lean_closure_set(v___f_4045_, 7, v___f_4033_);
v___x_4046_ = lean_apply_2(v_inst_4030_, lean_box(0), v___f_4043_);
v___x_4047_ = lean_apply_4(v_toBind_4031_, lean_box(0), lean_box(0), v___x_4046_, v___f_4045_);
return v___x_4047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4048_, lean_object* v_toPure_4049_, lean_object* v_levels_x3f_4050_, lean_object* v_inst_4051_, lean_object* v_toBind_4052_, lean_object* v_params_4053_, lean_object* v___f_4054_, lean_object* v_cinfo_4055_){
_start:
{
lean_object* v___f_4056_; 
lean_inc(v_toBind_4052_);
lean_inc(v_inst_4051_);
lean_inc(v_levels_x3f_4050_);
lean_inc(v_toPure_4049_);
lean_inc_ref(v_cinfo_4055_);
v___f_4056_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4056_, 0, v_cinfo_4055_);
lean_closure_set(v___f_4056_, 1, v_inst_4048_);
lean_closure_set(v___f_4056_, 2, v_toPure_4049_);
lean_closure_set(v___f_4056_, 3, v_levels_x3f_4050_);
lean_closure_set(v___f_4056_, 4, v_inst_4051_);
lean_closure_set(v___f_4056_, 5, v_toBind_4052_);
lean_closure_set(v___f_4056_, 6, v_params_4053_);
lean_closure_set(v___f_4056_, 7, v___f_4054_);
if (lean_obj_tag(v_levels_x3f_4050_) == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec(v_toPure_4049_);
v___x_4057_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4057_, 0, v_cinfo_4055_);
v___x_4058_ = lean_apply_2(v_inst_4051_, lean_box(0), v___x_4057_);
v___x_4059_ = lean_apply_4(v_toBind_4052_, lean_box(0), lean_box(0), v___x_4058_, v___f_4056_);
return v___x_4059_;
}
else
{
lean_object* v_val_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v_cinfo_4055_);
lean_dec(v_inst_4051_);
v_val_4060_ = lean_ctor_get(v_levels_x3f_4050_, 0);
lean_inc(v_val_4060_);
lean_dec_ref(v_levels_x3f_4050_);
v___x_4061_ = lean_apply_2(v_toPure_4049_, lean_box(0), v_val_4060_);
v___x_4062_ = lean_apply_4(v_toBind_4052_, lean_box(0), lean_box(0), v___x_4061_, v___f_4056_);
return v___x_4062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_inst_4066_, lean_object* v_defaultFn_4067_, lean_object* v_levels_x3f_4068_, lean_object* v_params_4069_, lean_object* v_fieldVal_x3f_4070_){
_start:
{
lean_object* v_toApplicative_4071_; lean_object* v_toBind_4072_; lean_object* v_toPure_4073_; lean_object* v___x_4074_; lean_object* v___f_4075_; lean_object* v___f_4076_; lean_object* v___x_4077_; 
v_toApplicative_4071_ = lean_ctor_get(v_inst_4063_, 0);
v_toBind_4072_ = lean_ctor_get(v_inst_4063_, 1);
lean_inc(v_toBind_4072_);
v_toPure_4073_ = lean_ctor_get(v_toApplicative_4071_, 1);
lean_inc(v_toPure_4073_);
lean_inc_ref(v_inst_4063_);
v___x_4074_ = l_Lean_getConstInfo___redArg(v_inst_4063_, v_inst_4064_, v_inst_4065_, v_defaultFn_4067_);
lean_inc(v_toPure_4073_);
lean_inc(v_inst_4066_);
lean_inc_ref(v_inst_4063_);
v___f_4075_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4075_, 0, v_inst_4063_);
lean_closure_set(v___f_4075_, 1, v_inst_4066_);
lean_closure_set(v___f_4075_, 2, v_fieldVal_x3f_4070_);
lean_closure_set(v___f_4075_, 3, v_toPure_4073_);
lean_inc(v_toBind_4072_);
v___f_4076_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4076_, 0, v_inst_4063_);
lean_closure_set(v___f_4076_, 1, v_toPure_4073_);
lean_closure_set(v___f_4076_, 2, v_levels_x3f_4068_);
lean_closure_set(v___f_4076_, 3, v_inst_4066_);
lean_closure_set(v___f_4076_, 4, v_toBind_4072_);
lean_closure_set(v___f_4076_, 5, v_params_4069_);
lean_closure_set(v___f_4076_, 6, v___f_4075_);
v___x_4077_ = lean_apply_4(v_toBind_4072_, lean_box(0), lean_box(0), v___x_4074_, v___f_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4078_, lean_object* v_inst_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_defaultFn_4084_, lean_object* v_levels_x3f_4085_, lean_object* v_params_4086_, lean_object* v_fieldVal_x3f_4087_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4079_, v_inst_4080_, v_inst_4081_, v_inst_4082_, v_defaultFn_4084_, v_levels_x3f_4085_, v_params_4086_, v_fieldVal_x3f_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4089_, lean_object* v_inst_4090_, lean_object* v_inst_4091_, lean_object* v_inst_4092_, lean_object* v_inst_4093_, lean_object* v_inst_4094_, lean_object* v_defaultFn_4095_, lean_object* v_levels_x3f_4096_, lean_object* v_params_4097_, lean_object* v_fieldVal_x3f_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4089_, v_inst_4090_, v_inst_4091_, v_inst_4092_, v_inst_4093_, v_inst_4094_, v_defaultFn_4095_, v_levels_x3f_4096_, v_params_4097_, v_fieldVal_x3f_4098_);
lean_dec_ref(v_inst_4094_);
return v_res_4099_;
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
