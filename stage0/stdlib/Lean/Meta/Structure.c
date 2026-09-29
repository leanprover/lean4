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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEIO___redArg();
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
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
static const lean_array_object l_Lean_Meta_mkProjections___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkProjections___closed__4 = (const lean_object*)&l_Lean_Meta_mkProjections___closed__4_value;
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_389_; lean_object* v_currRecDepth_390_; lean_object* v_ref_391_; uint16_t v_optionFlags_392_; uint8_t v_suppressElabErrors_393_; uint8_t v_isRecordingDeps_394_; lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_toCold_389_ = lean_ctor_get(v___y_386_, 0);
v_currRecDepth_390_ = lean_ctor_get(v___y_386_, 1);
v_ref_391_ = lean_ctor_get(v___y_386_, 2);
v_optionFlags_392_ = lean_ctor_get_uint16(v___y_386_, sizeof(void*)*3);
v_suppressElabErrors_393_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*3 + 2);
v_isRecordingDeps_394_ = lean_ctor_get_uint8(v___y_386_, sizeof(void*)*3 + 3);
v_ref_395_ = l_Lean_replaceRef(v_ref_382_, v_ref_391_);
lean_inc(v_currRecDepth_390_);
lean_inc_ref(v_toCold_389_);
v___x_396_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_396_, 0, v_toCold_389_);
lean_ctor_set(v___x_396_, 1, v_currRecDepth_390_);
lean_ctor_set(v___x_396_, 2, v_ref_395_);
lean_ctor_set_uint16(v___x_396_, sizeof(void*)*3, v_optionFlags_392_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 2, v_suppressElabErrors_393_);
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3 + 3, v_isRecordingDeps_394_);
v___x_397_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_, v___x_396_, v___y_387_);
lean_dec_ref_known(v___x_396_, 3);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_398_, lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_398_, v_msg_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v_ref_398_);
return v_res_405_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_414_ = l_Lean_stringToMessageData(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_415_, lean_object* v_projName_416_, lean_object* v_n_417_, lean_object* v_ref_418_, lean_object* v___f_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
if (v___x_415_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_425_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_426_ = l_Lean_MessageData_ofName(v_projName_416_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l_Lean_MessageData_ofConstName(v_n_417_, v___x_415_);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_418_, v___x_433_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_436_ = lean_apply_6(v___f_419_, v_a_435_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
return v___x_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec_ref(v___f_419_);
v_a_437_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_434_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_434_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_n_417_);
lean_dec(v_projName_416_);
v___x_445_ = lean_box(0);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_446_ = lean_apply_6(v___f_419_, v___x_445_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_447_, lean_object* v_projName_448_, lean_object* v_n_449_, lean_object* v_ref_450_, lean_object* v___f_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_17048__boxed_457_; lean_object* v_res_458_; 
v___x_17048__boxed_457_ = lean_unbox(v___x_447_);
v_res_458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17048__boxed_457_, v_projName_448_, v_n_449_, v_ref_450_, v___f_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v_ref_450_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_459_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_465_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
lean_ctor_set(v___x_465_, 2, v___x_464_);
lean_ctor_set(v___x_465_, 3, v___x_464_);
lean_ctor_set(v___x_465_, 4, v___x_464_);
lean_ctor_set(v___x_465_, 5, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_466_, uint8_t v_s_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; lean_object* v_env_472_; lean_object* v_nextMacroScope_473_; lean_object* v_ngen_474_; lean_object* v_auxDeclNGen_475_; lean_object* v_traceState_476_; lean_object* v_recordedDeps_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_509_; 
v___x_471_ = lean_st_ref_take(v___y_469_);
v_env_472_ = lean_ctor_get(v___x_471_, 0);
v_nextMacroScope_473_ = lean_ctor_get(v___x_471_, 1);
v_ngen_474_ = lean_ctor_get(v___x_471_, 2);
v_auxDeclNGen_475_ = lean_ctor_get(v___x_471_, 3);
v_traceState_476_ = lean_ctor_get(v___x_471_, 4);
v_recordedDeps_477_ = lean_ctor_get(v___x_471_, 6);
v_messages_478_ = lean_ctor_get(v___x_471_, 7);
v_infoState_479_ = lean_ctor_get(v___x_471_, 8);
v_snapshotTasks_480_ = lean_ctor_get(v___x_471_, 9);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_471_, 5);
lean_dec(v_unused_510_);
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_509_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snapshotTasks_480_);
lean_inc(v_infoState_479_);
lean_inc(v_messages_478_);
lean_inc(v_recordedDeps_477_);
lean_inc(v_traceState_476_);
lean_inc(v_auxDeclNGen_475_);
lean_inc(v_ngen_474_);
lean_inc(v_nextMacroScope_473_);
lean_inc(v_env_472_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_509_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_484_ = 0;
v___x_485_ = lean_box(0);
v___x_486_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_472_, v_declName_466_, v_s_467_, v___x_484_, v___x_485_);
v___x_487_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 5, v___x_487_);
lean_ctor_set(v___x_482_, 0, v___x_486_);
v___x_489_ = v___x_482_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_473_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_ngen_474_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_475_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_traceState_476_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_recordedDeps_477_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v_messages_478_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_508_, 9, v_snapshotTasks_480_);
v___x_489_ = v_reuseFailAlloc_508_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_mctx_492_; lean_object* v_zetaDeltaFVarIds_493_; lean_object* v_postponed_494_; lean_object* v_diag_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_506_; 
v___x_490_ = lean_st_ref_put(v___y_469_, v___x_489_);
v___x_491_ = lean_st_ref_take(v___y_468_);
v_mctx_492_ = lean_ctor_get(v___x_491_, 0);
v_zetaDeltaFVarIds_493_ = lean_ctor_get(v___x_491_, 2);
v_postponed_494_ = lean_ctor_get(v___x_491_, 3);
v_diag_495_ = lean_ctor_get(v___x_491_, 4);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v___x_491_, 1);
lean_dec(v_unused_507_);
v___x_497_ = v___x_491_;
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_diag_495_);
lean_inc(v_postponed_494_);
lean_inc(v_zetaDeltaFVarIds_493_);
lean_inc(v_mctx_492_);
lean_dec(v___x_491_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_506_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = lean_box(0);
v___x_500_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_mctx_492_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_zetaDeltaFVarIds_493_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v_postponed_494_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_diag_495_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_st_ref_put(v___y_468_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_499_);
return v___x_504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_511_, lean_object* v_s_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v_s_boxed_516_; lean_object* v_res_517_; 
v_s_boxed_516_ = lean_unbox(v_s_512_);
v_res_517_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_511_, v_s_boxed_516_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec(v___y_513_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; lean_object* v___x_525_; 
v___x_524_ = 0;
v___x_525_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_518_, v___x_524_, v___y_520_, v___y_522_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_542_, lean_object* v_projName_543_, lean_object* v___x_544_, lean_object* v_a_545_, uint8_t v_instImplicit_546_, lean_object* v___x_547_, lean_object* v_params_548_, lean_object* v_self_549_, lean_object* v_b_550_, uint8_t v___x_551_, lean_object* v_a_552_, lean_object* v___x_553_, lean_object* v_paramInfoOverrides_554_, lean_object* v_n_555_, lean_object* v_ref_556_, lean_object* v___x_557_, uint8_t v_a_558_, lean_object* v_____r_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; uint8_t v___y_628_; lean_object* v___y_629_; uint8_t v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = l_List_lengthTR___redArg(v_paramInfoOverrides_554_);
v___x_720_ = lean_array_get_size(v_params_548_);
v___x_721_ = lean_nat_dec_le(v___x_719_, v___x_720_);
lean_dec(v___x_719_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_722_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_543_);
v___x_723_ = l_Lean_MessageData_ofName(v_projName_543_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
lean_inc(v_n_555_);
v___x_727_ = l_Lean_MessageData_ofConstName(v_n_555_, v___x_721_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_556_, v___x_730_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
goto v___jp_680_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v___x_557_);
lean_dec(v_n_555_);
lean_dec_ref(v_a_552_);
lean_dec_ref(v_self_549_);
lean_dec(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v___x_544_);
lean_dec(v_projName_543_);
lean_dec_ref(v___x_542_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
goto v___jp_680_;
}
v___jp_565_:
{
lean_object* v___x_568_; lean_object* v_env_569_; lean_object* v_nextMacroScope_570_; lean_object* v_ngen_571_; lean_object* v_auxDeclNGen_572_; lean_object* v_traceState_573_; lean_object* v_recordedDeps_574_; lean_object* v_messages_575_; lean_object* v_infoState_576_; lean_object* v_snapshotTasks_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_609_; 
v___x_568_ = lean_st_ref_take(v___y_567_);
v_env_569_ = lean_ctor_get(v___x_568_, 0);
v_nextMacroScope_570_ = lean_ctor_get(v___x_568_, 1);
v_ngen_571_ = lean_ctor_get(v___x_568_, 2);
v_auxDeclNGen_572_ = lean_ctor_get(v___x_568_, 3);
v_traceState_573_ = lean_ctor_get(v___x_568_, 4);
v_recordedDeps_574_ = lean_ctor_get(v___x_568_, 6);
v_messages_575_ = lean_ctor_get(v___x_568_, 7);
v_infoState_576_ = lean_ctor_get(v___x_568_, 8);
v_snapshotTasks_577_ = lean_ctor_get(v___x_568_, 9);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_568_, 5);
lean_dec(v_unused_610_);
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snapshotTasks_577_);
lean_inc(v_infoState_576_);
lean_inc(v_messages_575_);
lean_inc(v_recordedDeps_574_);
lean_inc(v_traceState_573_);
lean_inc(v_auxDeclNGen_572_);
lean_inc(v_ngen_571_);
lean_inc(v_nextMacroScope_570_);
lean_inc(v_env_569_);
lean_dec(v___x_568_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_609_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_name_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_name_581_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_name_581_);
lean_dec_ref(v___x_542_);
lean_inc(v_projName_543_);
v___x_582_ = l_Lean_addProjectionFnInfo(v_env_569_, v_projName_543_, v_name_581_, v___x_544_, v_a_545_, v_instImplicit_546_);
v___x_583_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 5, v___x_583_);
lean_ctor_set(v___x_579_, 0, v___x_582_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_570_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_571_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_572_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_traceState_573_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_recordedDeps_574_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_messages_575_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_snapshotTasks_577_);
v___x_585_ = v_reuseFailAlloc_608_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_mctx_588_; lean_object* v_zetaDeltaFVarIds_589_; lean_object* v_postponed_590_; lean_object* v_diag_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_606_; 
v___x_586_ = lean_st_ref_put(v___y_567_, v___x_585_);
v___x_587_ = lean_st_ref_take(v___y_566_);
v_mctx_588_ = lean_ctor_get(v___x_587_, 0);
v_zetaDeltaFVarIds_589_ = lean_ctor_get(v___x_587_, 2);
v_postponed_590_ = lean_ctor_get(v___x_587_, 3);
v_diag_591_ = lean_ctor_get(v___x_587_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_587_, 1);
lean_dec(v_unused_607_);
v___x_593_ = v___x_587_;
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_diag_591_);
lean_inc(v_postponed_590_);
lean_inc(v_zetaDeltaFVarIds_589_);
lean_inc(v_mctx_588_);
lean_dec(v___x_587_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_mctx_588_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_zetaDeltaFVarIds_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_postponed_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_diag_591_);
v___x_597_ = v_reuseFailAlloc_605_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_598_ = lean_st_ref_put(v___y_566_, v___x_597_);
v___x_599_ = l_Lean_Expr_const___override(v_projName_543_, v___x_547_);
v___x_600_ = l_Lean_mkAppN(v___x_599_, v_params_548_);
v___x_601_ = l_Lean_Expr_app___override(v___x_600_, v_self_549_);
v___x_602_ = l_Lean_Expr_bindingBody_x21(v_b_550_);
v___x_603_ = lean_expr_instantiate1(v___x_602_, v___x_601_);
lean_dec_ref(v___x_601_);
lean_dec_ref(v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
}
}
v___jp_611_:
{
if (lean_obj_tag(v___y_614_) == 0)
{
lean_dec_ref_known(v___y_614_, 1);
v___y_566_ = v___y_612_;
v___y_567_ = v___y_613_;
goto v___jp_565_;
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_self_549_);
lean_dec(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v___x_544_);
lean_dec(v_projName_543_);
lean_dec_ref(v___x_542_);
v_a_615_ = lean_ctor_get(v___y_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___y_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___y_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___y_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
v___jp_623_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = lean_box(0);
lean_inc(v_projName_543_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v_projName_543_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_632_, 0, v___y_625_);
lean_ctor_set(v___x_632_, 1, v___y_624_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3, v___x_551_);
v___x_633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = l_Lean_addDecl(v___x_633_, v___y_628_, v___y_627_, v___y_629_);
lean_dec_ref(v___y_627_);
v___y_612_ = v___y_626_;
v___y_613_ = v___y_629_;
v___y_614_ = v___x_634_;
goto v___jp_611_;
}
v___jp_635_:
{
uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v_toCold_644_; lean_object* v_currRecDepth_645_; lean_object* v_ref_646_; uint16_t v_optionFlags_647_; uint8_t v_suppressElabErrors_648_; uint8_t v_isRecordingDeps_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_ref_654_; lean_object* v___x_655_; 
v___x_642_ = 0;
lean_inc_ref(v_a_552_);
v___x_643_ = l_Lean_LocalContext_mkForall(v_a_552_, v___x_553_, v___y_637_, v___x_551_, v___x_642_);
lean_dec_ref(v___y_637_);
v_toCold_644_ = lean_ctor_get(v___y_640_, 0);
v_currRecDepth_645_ = lean_ctor_get(v___y_640_, 1);
v_ref_646_ = lean_ctor_get(v___y_640_, 2);
v_optionFlags_647_ = lean_ctor_get_uint16(v___y_640_, sizeof(void*)*3);
v_suppressElabErrors_648_ = lean_ctor_get_uint8(v___y_640_, sizeof(void*)*3 + 2);
v_isRecordingDeps_649_ = lean_ctor_get_uint8(v___y_640_, sizeof(void*)*3 + 3);
v___x_650_ = l_Lean_Expr_inferImplicit(v___x_643_, v___x_544_, v___x_551_);
v___x_651_ = l_Lean_Expr_updateForallBinderInfos(v___x_650_, v_paramInfoOverrides_554_);
lean_inc_ref(v_self_549_);
lean_inc(v_a_545_);
v___x_652_ = l_Lean_Expr_proj___override(v_n_555_, v_a_545_, v_self_549_);
v___x_653_ = l_Lean_LocalContext_mkLambda(v_a_552_, v___x_553_, v___x_652_, v___x_551_, v___x_642_);
lean_dec_ref(v___x_652_);
v_ref_654_ = l_Lean_replaceRef(v_ref_556_, v_ref_646_);
lean_inc(v_currRecDepth_645_);
lean_inc_ref(v_toCold_644_);
v___x_655_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_655_, 0, v_toCold_644_);
lean_ctor_set(v___x_655_, 1, v_currRecDepth_645_);
lean_ctor_set(v___x_655_, 2, v_ref_654_);
lean_ctor_set_uint16(v___x_655_, sizeof(void*)*3, v_optionFlags_647_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 2, v_suppressElabErrors_648_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 3, v_isRecordingDeps_649_);
if (v___y_636_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_box(1);
lean_inc(v_projName_543_);
v___x_657_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_543_, v___x_557_, v___x_651_, v___x_653_, v___x_656_, v___y_641_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_a_658_);
v___x_660_ = l_Lean_addDecl(v___x_659_, v___x_642_, v___x_655_, v___y_641_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_dec_ref_known(v___x_660_, 1);
if (v_instImplicit_546_ == 0)
{
lean_object* v___x_661_; 
lean_inc(v_projName_543_);
v___x_661_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_543_, v___y_638_, v___y_639_, v___x_655_, v___y_641_);
lean_dec_ref_known(v___x_655_, 3);
v___y_612_ = v___y_639_;
v___y_613_ = v___y_641_;
v___y_614_ = v___x_661_;
goto v___jp_611_;
}
else
{
lean_dec_ref_known(v___x_655_, 3);
v___y_566_ = v___y_639_;
v___y_567_ = v___y_641_;
goto v___jp_565_;
}
}
else
{
lean_dec_ref_known(v___x_655_, 3);
v___y_612_ = v___y_639_;
v___y_613_ = v___y_641_;
v___y_614_ = v___x_660_;
goto v___jp_611_;
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref_known(v___x_655_, 3);
lean_dec_ref(v_self_549_);
lean_dec(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v___x_544_);
lean_dec(v_projName_543_);
lean_dec_ref(v___x_542_);
v_a_662_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_657_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_657_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v_env_672_; uint8_t v___x_673_; 
lean_inc_ref(v___x_651_);
lean_inc(v_projName_543_);
v___x_670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_670_, 0, v_projName_543_);
lean_ctor_set(v___x_670_, 1, v___x_557_);
lean_ctor_set(v___x_670_, 2, v___x_651_);
v___x_671_ = lean_st_ref_get(v___y_641_);
v_env_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_ref_n(v_env_672_, 2);
lean_dec(v___x_671_);
v___x_673_ = l_Lean_Environment_hasUnsafe(v_env_672_, v___x_651_);
lean_dec_ref(v___x_651_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; 
v___x_674_ = l_Lean_Environment_hasUnsafe(v_env_672_, v___x_653_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_675_ = lean_box(0);
lean_inc(v_projName_543_);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v_projName_543_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_677_, 0, v___x_670_);
lean_ctor_set(v___x_677_, 1, v___x_653_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
v___x_678_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v___x_679_ = l_Lean_addDecl(v___x_678_, v___x_642_, v___x_655_, v___y_641_);
lean_dec_ref_known(v___x_655_, 3);
v___y_612_ = v___y_639_;
v___y_613_ = v___y_641_;
v___y_614_ = v___x_679_;
goto v___jp_611_;
}
else
{
v___y_624_ = v___x_653_;
v___y_625_ = v___x_670_;
v___y_626_ = v___y_639_;
v___y_627_ = v___x_655_;
v___y_628_ = v___x_642_;
v___y_629_ = v___y_641_;
goto v___jp_623_;
}
}
else
{
lean_dec_ref(v_env_672_);
v___y_624_ = v___x_653_;
v___y_625_ = v___x_670_;
v___y_626_ = v___y_639_;
v___y_627_ = v___x_655_;
v___y_628_ = v___x_642_;
v___y_629_ = v___y_641_;
goto v___jp_623_;
}
}
}
v___jp_680_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_Expr_bindingDomain_x21(v_b_550_);
v___x_682_ = lean_expr_consume_type_annotations(v___x_681_);
lean_inc_ref(v___x_682_);
v___x_683_ = l_Lean_Meta_isProp(v___x_682_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_683_) == 0)
{
if (v_a_558_ == 0)
{
lean_object* v_a_684_; uint8_t v___x_685_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = lean_unbox(v_a_684_);
lean_dec(v_a_684_);
v___y_636_ = v___x_685_;
v___y_637_ = v___x_682_;
v___y_638_ = v___y_560_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
goto v___jp_635_;
}
else
{
lean_object* v_a_686_; uint8_t v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_683_, 1);
v___x_687_ = lean_unbox(v_a_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_688_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_543_);
v___x_689_ = l_Lean_MessageData_ofName(v_projName_543_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_unbox(v_a_686_);
lean_inc(v_n_555_);
v___x_694_ = l_Lean_MessageData_ofConstName(v_n_555_, v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_692_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_inc_ref(v___x_682_);
v___x_698_ = l_Lean_indentExpr(v___x_682_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_556_, v___x_699_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_700_) == 0)
{
uint8_t v___x_701_; 
lean_dec_ref_known(v___x_700_, 1);
v___x_701_ = lean_unbox(v_a_686_);
lean_dec(v_a_686_);
v___y_636_ = v___x_701_;
v___y_637_ = v___x_682_;
v___y_638_ = v___y_560_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
goto v___jp_635_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_a_686_);
lean_dec_ref(v___x_682_);
lean_dec(v___x_557_);
lean_dec(v_n_555_);
lean_dec_ref(v_a_552_);
lean_dec_ref(v_self_549_);
lean_dec(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v___x_544_);
lean_dec(v_projName_543_);
lean_dec_ref(v___x_542_);
v_a_702_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_700_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_unbox(v_a_686_);
lean_dec(v_a_686_);
v___y_636_ = v___x_710_;
v___y_637_ = v___x_682_;
v___y_638_ = v___y_560_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
goto v___jp_635_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___x_682_);
lean_dec(v___x_557_);
lean_dec(v_n_555_);
lean_dec_ref(v_a_552_);
lean_dec_ref(v_self_549_);
lean_dec(v___x_547_);
lean_dec(v_a_545_);
lean_dec(v___x_544_);
lean_dec(v_projName_543_);
lean_dec_ref(v___x_542_);
v_a_711_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_683_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_683_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_740_ = _args[0];
lean_object* v_projName_741_ = _args[1];
lean_object* v___x_742_ = _args[2];
lean_object* v_a_743_ = _args[3];
lean_object* v_instImplicit_744_ = _args[4];
lean_object* v___x_745_ = _args[5];
lean_object* v_params_746_ = _args[6];
lean_object* v_self_747_ = _args[7];
lean_object* v_b_748_ = _args[8];
lean_object* v___x_749_ = _args[9];
lean_object* v_a_750_ = _args[10];
lean_object* v___x_751_ = _args[11];
lean_object* v_paramInfoOverrides_752_ = _args[12];
lean_object* v_n_753_ = _args[13];
lean_object* v_ref_754_ = _args[14];
lean_object* v___x_755_ = _args[15];
lean_object* v_a_756_ = _args[16];
lean_object* v_____r_757_ = _args[17];
lean_object* v___y_758_ = _args[18];
lean_object* v___y_759_ = _args[19];
lean_object* v___y_760_ = _args[20];
lean_object* v___y_761_ = _args[21];
lean_object* v___y_762_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_763_; uint8_t v___x_17287__boxed_764_; uint8_t v_a_17293__boxed_765_; lean_object* v_res_766_; 
v_instImplicit_boxed_763_ = lean_unbox(v_instImplicit_744_);
v___x_17287__boxed_764_ = lean_unbox(v___x_749_);
v_a_17293__boxed_765_ = lean_unbox(v_a_756_);
v_res_766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_740_, v_projName_741_, v___x_742_, v_a_743_, v_instImplicit_boxed_763_, v___x_745_, v_params_746_, v_self_747_, v_b_748_, v___x_17287__boxed_764_, v_a_750_, v___x_751_, v_paramInfoOverrides_752_, v_n_753_, v_ref_754_, v___x_755_, v_a_17293__boxed_765_, v_____r_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v_ref_754_);
lean_dec(v_paramInfoOverrides_752_);
lean_dec_ref(v___x_751_);
lean_dec_ref(v_b_748_);
lean_dec_ref(v_params_746_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_767_, uint8_t v_isExporting_768_, lean_object* v___x_769_, lean_object* v___y_770_, lean_object* v___x_771_, lean_object* v_a_x3f_772_){
_start:
{
lean_object* v___x_774_; lean_object* v_env_775_; lean_object* v_nextMacroScope_776_; lean_object* v_ngen_777_; lean_object* v_auxDeclNGen_778_; lean_object* v_traceState_779_; lean_object* v_recordedDeps_780_; lean_object* v_messages_781_; lean_object* v_infoState_782_; lean_object* v_snapshotTasks_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_808_; 
v___x_774_ = lean_st_ref_take(v___y_767_);
v_env_775_ = lean_ctor_get(v___x_774_, 0);
v_nextMacroScope_776_ = lean_ctor_get(v___x_774_, 1);
v_ngen_777_ = lean_ctor_get(v___x_774_, 2);
v_auxDeclNGen_778_ = lean_ctor_get(v___x_774_, 3);
v_traceState_779_ = lean_ctor_get(v___x_774_, 4);
v_recordedDeps_780_ = lean_ctor_get(v___x_774_, 6);
v_messages_781_ = lean_ctor_get(v___x_774_, 7);
v_infoState_782_ = lean_ctor_get(v___x_774_, 8);
v_snapshotTasks_783_ = lean_ctor_get(v___x_774_, 9);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_774_, 5);
lean_dec(v_unused_809_);
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snapshotTasks_783_);
lean_inc(v_infoState_782_);
lean_inc(v_messages_781_);
lean_inc(v_recordedDeps_780_);
lean_inc(v_traceState_779_);
lean_inc(v_auxDeclNGen_778_);
lean_inc(v_ngen_777_);
lean_inc(v_nextMacroScope_776_);
lean_inc(v_env_775_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = l_Lean_Environment_setExporting(v_env_775_, v_isExporting_768_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 5, v___x_769_);
lean_ctor_set(v___x_785_, 0, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_nextMacroScope_776_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_ngen_777_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_auxDeclNGen_778_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_traceState_779_);
lean_ctor_set(v_reuseFailAlloc_807_, 5, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_807_, 6, v_recordedDeps_780_);
lean_ctor_set(v_reuseFailAlloc_807_, 7, v_messages_781_);
lean_ctor_set(v_reuseFailAlloc_807_, 8, v_infoState_782_);
lean_ctor_set(v_reuseFailAlloc_807_, 9, v_snapshotTasks_783_);
v___x_789_ = v_reuseFailAlloc_807_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_mctx_792_; lean_object* v_zetaDeltaFVarIds_793_; lean_object* v_postponed_794_; lean_object* v_diag_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
v___x_790_ = lean_st_ref_put(v___y_767_, v___x_789_);
v___x_791_ = lean_st_ref_take(v___y_770_);
v_mctx_792_ = lean_ctor_get(v___x_791_, 0);
v_zetaDeltaFVarIds_793_ = lean_ctor_get(v___x_791_, 2);
v_postponed_794_ = lean_ctor_get(v___x_791_, 3);
v_diag_795_ = lean_ctor_get(v___x_791_, 4);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v___x_791_, 1);
lean_dec(v_unused_806_);
v___x_797_ = v___x_791_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_diag_795_);
lean_inc(v_postponed_794_);
lean_inc(v_zetaDeltaFVarIds_793_);
lean_inc(v_mctx_792_);
lean_dec(v___x_791_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_771_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_mctx_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_zetaDeltaFVarIds_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_postponed_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_diag_795_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_st_ref_put(v___y_770_, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_799_);
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_810_, lean_object* v_isExporting_811_, lean_object* v___x_812_, lean_object* v___y_813_, lean_object* v___x_814_, lean_object* v_a_x3f_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_isExporting_boxed_817_; lean_object* v_res_818_; 
v_isExporting_boxed_817_ = lean_unbox(v_isExporting_811_);
v_res_818_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_810_, v_isExporting_boxed_817_, v___x_812_, v___y_813_, v___x_814_, v_a_x3f_815_);
lean_dec(v_a_x3f_815_);
lean_dec(v___y_813_);
lean_dec(v___y_810_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_819_, uint8_t v_isExporting_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_env_827_; lean_object* v___x_828_; uint8_t v_isModule_829_; 
v___x_826_ = lean_st_ref_get(v___y_824_);
v_env_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref(v_env_827_);
lean_dec(v___x_826_);
v___x_828_ = l_Lean_Environment_header(v_env_827_);
v_isModule_829_ = lean_ctor_get_uint8(v___x_828_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_828_);
if (v_isModule_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref(v_env_827_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
v___x_830_ = lean_apply_5(v_x_819_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, lean_box(0));
return v___x_830_;
}
else
{
uint8_t v_isExporting_831_; 
v_isExporting_831_ = lean_ctor_get_uint8(v_env_827_, sizeof(void*)*8);
lean_dec_ref(v_env_827_);
if (v_isExporting_820_ == 0)
{
if (v_isExporting_831_ == 0)
{
lean_object* v___x_898_; 
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
v___x_898_ = lean_apply_5(v_x_819_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, lean_box(0));
return v___x_898_;
}
else
{
goto v___jp_832_;
}
}
else
{
if (v_isExporting_831_ == 0)
{
goto v___jp_832_;
}
else
{
lean_object* v___x_899_; 
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
v___x_899_ = lean_apply_5(v_x_819_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, lean_box(0));
return v___x_899_;
}
}
v___jp_832_:
{
lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v_nextMacroScope_835_; lean_object* v_ngen_836_; lean_object* v_auxDeclNGen_837_; lean_object* v_traceState_838_; lean_object* v_recordedDeps_839_; lean_object* v_messages_840_; lean_object* v_infoState_841_; lean_object* v_snapshotTasks_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_896_; 
v___x_833_ = lean_st_ref_take(v___y_824_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
v_nextMacroScope_835_ = lean_ctor_get(v___x_833_, 1);
v_ngen_836_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_837_ = lean_ctor_get(v___x_833_, 3);
v_traceState_838_ = lean_ctor_get(v___x_833_, 4);
v_recordedDeps_839_ = lean_ctor_get(v___x_833_, 6);
v_messages_840_ = lean_ctor_get(v___x_833_, 7);
v_infoState_841_ = lean_ctor_get(v___x_833_, 8);
v_snapshotTasks_842_ = lean_ctor_get(v___x_833_, 9);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_833_, 5);
lean_dec(v_unused_897_);
v___x_844_ = v___x_833_;
v_isShared_845_ = v_isSharedCheck_896_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snapshotTasks_842_);
lean_inc(v_infoState_841_);
lean_inc(v_messages_840_);
lean_inc(v_recordedDeps_839_);
lean_inc(v_traceState_838_);
lean_inc(v_auxDeclNGen_837_);
lean_inc(v_ngen_836_);
lean_inc(v_nextMacroScope_835_);
lean_inc(v_env_834_);
lean_dec(v___x_833_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_896_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = l_Lean_Environment_setExporting(v_env_834_, v_isExporting_820_);
v___x_847_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 5, v___x_847_);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_nextMacroScope_835_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_ngen_836_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_auxDeclNGen_837_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_traceState_838_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_recordedDeps_839_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_messages_840_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_infoState_841_);
lean_ctor_set(v_reuseFailAlloc_895_, 9, v_snapshotTasks_842_);
v___x_849_ = v_reuseFailAlloc_895_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_mctx_852_; lean_object* v_zetaDeltaFVarIds_853_; lean_object* v_postponed_854_; lean_object* v_diag_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_893_; 
v___x_850_ = lean_st_ref_put(v___y_824_, v___x_849_);
v___x_851_ = lean_st_ref_take(v___y_822_);
v_mctx_852_ = lean_ctor_get(v___x_851_, 0);
v_zetaDeltaFVarIds_853_ = lean_ctor_get(v___x_851_, 2);
v_postponed_854_ = lean_ctor_get(v___x_851_, 3);
v_diag_855_ = lean_ctor_get(v___x_851_, 4);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_851_, 1);
lean_dec(v_unused_894_);
v___x_857_ = v___x_851_;
v_isShared_858_ = v_isSharedCheck_893_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_diag_855_);
lean_inc(v_postponed_854_);
lean_inc(v_zetaDeltaFVarIds_853_);
lean_inc(v_mctx_852_);
lean_dec(v___x_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_893_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_mctx_852_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_zetaDeltaFVarIds_853_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_postponed_854_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_diag_855_);
v___x_861_ = v_reuseFailAlloc_892_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v_r_863_; 
v___x_862_ = lean_st_ref_put(v___y_822_, v___x_861_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
v_r_863_ = lean_apply_5(v_x_819_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, lean_box(0));
if (lean_obj_tag(v_r_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_880_; 
v_a_864_ = lean_ctor_get(v_r_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_r_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_866_ = v_r_863_;
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v_r_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
lean_inc(v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set_tag(v___x_866_, 1);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_879_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v___x_870_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_824_, v_isExporting_831_, v___x_847_, v___y_822_, v___x_859_, v___x_869_);
lean_dec_ref(v___x_869_);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_878_);
v___x_872_ = v___x_870_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_dec(v___x_870_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_a_864_);
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_864_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_881_ = lean_ctor_get(v_r_863_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v_r_863_, 1);
v___x_882_ = lean_box(0);
v___x_883_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_824_, v_isExporting_831_, v___x_847_, v___y_822_, v___x_859_, v___x_882_);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_891_);
v___x_885_ = v___x_883_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 1);
lean_ctor_set(v___x_885_, 0, v_a_881_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_881_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_900_, lean_object* v_isExporting_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v_isExporting_boxed_907_; lean_object* v_res_908_; 
v_isExporting_boxed_907_ = lean_unbox(v_isExporting_901_);
v_res_908_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_900_, v_isExporting_boxed_907_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_909_, uint8_t v_when_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
if (v_when_910_ == 0)
{
lean_object* v___x_916_; 
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
v___x_916_ = lean_apply_5(v_x_909_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_916_;
}
else
{
uint8_t v___x_917_; lean_object* v___x_918_; 
v___x_917_ = 0;
v___x_918_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_909_, v___x_917_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_919_, lean_object* v_when_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_when_boxed_926_; lean_object* v_res_927_; 
v_when_boxed_926_ = lean_unbox(v_when_920_);
v_res_927_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_919_, v_when_boxed_926_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_928_, lean_object* v_projDecls_929_, lean_object* v___x_930_, lean_object* v___x_931_, uint8_t v_instImplicit_932_, lean_object* v___x_933_, lean_object* v_params_934_, lean_object* v_self_935_, lean_object* v_a_936_, lean_object* v___x_937_, lean_object* v_n_938_, lean_object* v___x_939_, uint8_t v_a_940_, lean_object* v_a_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_nat_dec_lt(v_a_941_, v_upperBound_928_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v_a_941_);
lean_dec(v___x_939_);
lean_dec(v_n_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_self_935_);
lean_dec_ref(v_params_934_);
lean_dec(v___x_933_);
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_942_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v_ref_951_; lean_object* v_projName_952_; lean_object* v_paramInfoOverrides_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___f_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___y_960_; uint8_t v___x_961_; lean_object* v___x_962_; 
v___x_950_ = lean_array_fget_borrowed(v_projDecls_929_, v_a_941_);
v_ref_951_ = lean_ctor_get(v___x_950_, 0);
v_projName_952_ = lean_ctor_get(v___x_950_, 1);
v_paramInfoOverrides_953_ = lean_ctor_get(v___x_950_, 2);
v___x_954_ = lean_box(v_instImplicit_932_);
v___x_955_ = lean_box(v___x_948_);
v___x_956_ = lean_box(v_a_940_);
lean_inc(v___x_939_);
lean_inc_n(v_ref_951_, 2);
lean_inc_n(v_n_938_, 2);
lean_inc(v_paramInfoOverrides_953_);
lean_inc_ref(v___x_937_);
lean_inc_ref(v_a_936_);
lean_inc_ref(v_b_942_);
lean_inc_ref(v_self_935_);
lean_inc_ref(v_params_934_);
lean_inc(v___x_933_);
lean_inc(v_a_941_);
lean_inc(v___x_931_);
lean_inc_n(v_projName_952_, 2);
lean_inc_ref(v___x_930_);
v___f_957_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_957_, 0, v___x_930_);
lean_closure_set(v___f_957_, 1, v_projName_952_);
lean_closure_set(v___f_957_, 2, v___x_931_);
lean_closure_set(v___f_957_, 3, v_a_941_);
lean_closure_set(v___f_957_, 4, v___x_954_);
lean_closure_set(v___f_957_, 5, v___x_933_);
lean_closure_set(v___f_957_, 6, v_params_934_);
lean_closure_set(v___f_957_, 7, v_self_935_);
lean_closure_set(v___f_957_, 8, v_b_942_);
lean_closure_set(v___f_957_, 9, v___x_955_);
lean_closure_set(v___f_957_, 10, v_a_936_);
lean_closure_set(v___f_957_, 11, v___x_937_);
lean_closure_set(v___f_957_, 12, v_paramInfoOverrides_953_);
lean_closure_set(v___f_957_, 13, v_n_938_);
lean_closure_set(v___f_957_, 14, v_ref_951_);
lean_closure_set(v___f_957_, 15, v___x_939_);
lean_closure_set(v___f_957_, 16, v___x_956_);
v___x_958_ = l_Lean_Expr_isForall(v_b_942_);
lean_dec_ref(v_b_942_);
v___x_959_ = lean_box(v___x_958_);
v___y_960_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_960_, 0, v___x_959_);
lean_closure_set(v___y_960_, 1, v_projName_952_);
lean_closure_set(v___y_960_, 2, v_n_938_);
lean_closure_set(v___y_960_, 3, v_ref_951_);
lean_closure_set(v___y_960_, 4, v___f_957_);
v___x_961_ = l_Lean_isPrivateName(v_projName_952_);
v___x_962_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_960_, v___x_961_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_add(v_a_941_, v___x_964_);
lean_dec(v_a_941_);
v_a_941_ = v___x_965_;
v_b_942_ = v_a_963_;
goto _start;
}
else
{
lean_dec(v_a_941_);
lean_dec(v___x_939_);
lean_dec(v_n_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_self_935_);
lean_dec_ref(v_params_934_);
lean_dec(v___x_933_);
lean_dec(v___x_931_);
lean_dec_ref(v___x_930_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_967_ = _args[0];
lean_object* v_projDecls_968_ = _args[1];
lean_object* v___x_969_ = _args[2];
lean_object* v___x_970_ = _args[3];
lean_object* v_instImplicit_971_ = _args[4];
lean_object* v___x_972_ = _args[5];
lean_object* v_params_973_ = _args[6];
lean_object* v_self_974_ = _args[7];
lean_object* v_a_975_ = _args[8];
lean_object* v___x_976_ = _args[9];
lean_object* v_n_977_ = _args[10];
lean_object* v___x_978_ = _args[11];
lean_object* v_a_979_ = _args[12];
lean_object* v_a_980_ = _args[13];
lean_object* v_b_981_ = _args[14];
lean_object* v___y_982_ = _args[15];
lean_object* v___y_983_ = _args[16];
lean_object* v___y_984_ = _args[17];
lean_object* v___y_985_ = _args[18];
lean_object* v___y_986_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_987_; uint8_t v_a_17890__boxed_988_; lean_object* v_res_989_; 
v_instImplicit_boxed_987_ = lean_unbox(v_instImplicit_971_);
v_a_17890__boxed_988_ = lean_unbox(v_a_979_);
v_res_989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_967_, v_projDecls_968_, v___x_969_, v___x_970_, v_instImplicit_boxed_987_, v___x_972_, v_params_973_, v_self_974_, v_a_975_, v___x_976_, v_n_977_, v___x_978_, v_a_17890__boxed_988_, v_a_980_, v_b_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_projDecls_968_);
lean_dec(v_upperBound_967_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_990_, lean_object* v_as_991_, size_t v_sz_992_, size_t v_i_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_a_1000_; uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_lt(v_i_993_, v_sz_992_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_b_994_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1006_ = lean_array_uget_borrowed(v_as_991_, v_i_993_);
v___x_1007_ = l_Lean_Expr_fvarId_x21(v_a_1006_);
lean_inc(v___x_1007_);
v___x_1008_ = l_Lean_FVarId_getDecl___redArg(v___x_1007_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; uint8_t v___y_1011_; uint8_t v___x_1014_; uint8_t v___x_1015_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1014_ = l_Lean_LocalDecl_binderInfo(v_a_1009_);
v___x_1015_ = l_Lean_BinderInfo_isInstImplicit(v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = l_Lean_LocalDecl_type(v_a_1009_);
lean_dec(v_a_1009_);
v___x_1018_ = l_Lean_Expr_isOutParam(v___x_1017_);
lean_dec_ref(v___x_1017_);
if (v___x_1018_ == 0)
{
uint8_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = 0;
v___x_1020_ = l_Lean_LocalContext_setBinderInfo(v_b_994_, v___x_1007_, v___x_1019_);
v_a_1000_ = v___x_1020_;
goto v___jp_999_;
}
else
{
goto v___jp_1016_;
}
}
else
{
lean_dec(v_a_1009_);
goto v___jp_1016_;
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
lean_dec(v___x_1007_);
v_a_1000_ = v_b_994_;
goto v___jp_999_;
}
else
{
uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = 1;
v___x_1013_ = l_Lean_LocalContext_setBinderInfo(v_b_994_, v___x_1007_, v___x_1012_);
v_a_1000_ = v___x_1013_;
goto v___jp_999_;
}
}
v___jp_1016_:
{
if (v___x_1015_ == 0)
{
v___y_1011_ = v___x_1015_;
goto v___jp_1010_;
}
else
{
v___y_1011_ = v_instImplicit_990_;
goto v___jp_1010_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___x_1007_);
lean_dec_ref(v_b_994_);
v_a_1021_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1008_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1008_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
v___jp_999_:
{
size_t v___x_1001_; size_t v___x_1002_; 
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_993_, v___x_1001_);
v_i_993_ = v___x_1002_;
v_b_994_ = v_a_1000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1029_, lean_object* v_as_1030_, lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v_instImplicit_boxed_1038_; size_t v_sz_boxed_1039_; size_t v_i_boxed_1040_; lean_object* v_res_1041_; 
v_instImplicit_boxed_1038_ = lean_unbox(v_instImplicit_1029_);
v_sz_boxed_1039_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1040_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1038_, v_as_1030_, v_sz_boxed_1039_, v_i_boxed_1040_, v_b_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec_ref(v_as_1030_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1042_, uint8_t v_instImplicit_1043_, lean_object* v_projDecls_1044_, lean_object* v_toConstantVal_1045_, lean_object* v_numParams_1046_, lean_object* v___x_1047_, lean_object* v_n_1048_, lean_object* v_levelParams_1049_, uint8_t v_a_1050_, lean_object* v_ctorType_1051_, lean_object* v_self_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_lctx_1058_; lean_object* v___x_1059_; size_t v_sz_1060_; size_t v___x_1061_; lean_object* v___x_1062_; 
v_lctx_1058_ = lean_ctor_get(v___y_1053_, 2);
lean_inc_ref(v_self_1052_);
lean_inc_ref(v_params_1042_);
v___x_1059_ = lean_array_push(v_params_1042_, v_self_1052_);
v_sz_1060_ = lean_array_size(v_params_1042_);
v___x_1061_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1058_);
v___x_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1043_, v_params_1042_, v_sz_1060_, v___x_1061_, v_lctx_1058_, v___y_1053_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_array_get_size(v_projDecls_1044_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1064_, v_projDecls_1044_, v_toConstantVal_1045_, v_numParams_1046_, v_instImplicit_1043_, v___x_1047_, v_params_1042_, v_self_1052_, v_a_1063_, v___x_1059_, v_n_1048_, v_levelParams_1049_, v_a_1050_, v___x_1065_, v_ctorType_1051_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1074_; 
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v___x_1066_, 0);
lean_dec(v_unused_1075_);
v___x_1068_ = v___x_1066_;
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v___x_1066_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1074_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_box(0);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1066_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1066_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v___x_1059_);
lean_dec_ref(v_self_1052_);
lean_dec_ref(v_ctorType_1051_);
lean_dec(v_levelParams_1049_);
lean_dec(v_n_1048_);
lean_dec(v___x_1047_);
lean_dec(v_numParams_1046_);
lean_dec_ref(v_toConstantVal_1045_);
lean_dec_ref(v_params_1042_);
v_a_1084_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1062_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1062_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1092_, lean_object* v_instImplicit_1093_, lean_object* v_projDecls_1094_, lean_object* v_toConstantVal_1095_, lean_object* v_numParams_1096_, lean_object* v___x_1097_, lean_object* v_n_1098_, lean_object* v_levelParams_1099_, lean_object* v_a_1100_, lean_object* v_ctorType_1101_, lean_object* v_self_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v_instImplicit_boxed_1108_; uint8_t v_a_18032__boxed_1109_; lean_object* v_res_1110_; 
v_instImplicit_boxed_1108_ = lean_unbox(v_instImplicit_1093_);
v_a_18032__boxed_1109_ = lean_unbox(v_a_1100_);
v_res_1110_ = l_Lean_Meta_mkProjections___lam__0(v_params_1092_, v_instImplicit_boxed_1108_, v_projDecls_1094_, v_toConstantVal_1095_, v_numParams_1096_, v___x_1097_, v_n_1098_, v_levelParams_1099_, v_a_18032__boxed_1109_, v_ctorType_1101_, v_self_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v_projDecls_1094_);
return v_res_1110_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1120_, lean_object* v_projDecls_1121_, lean_object* v_toConstantVal_1122_, lean_object* v_numParams_1123_, lean_object* v___x_1124_, lean_object* v_n_1125_, lean_object* v_levelParams_1126_, uint8_t v_a_1127_, lean_object* v_params_1128_, lean_object* v_ctorType_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1146_ = lean_box(v_instImplicit_1120_);
v___x_1147_ = lean_box(v_a_1127_);
lean_inc(v_n_1125_);
lean_inc(v___x_1124_);
lean_inc(v_numParams_1123_);
lean_inc_ref(v_params_1128_);
v___f_1148_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1148_, 0, v_params_1128_);
lean_closure_set(v___f_1148_, 1, v___x_1146_);
lean_closure_set(v___f_1148_, 2, v_projDecls_1121_);
lean_closure_set(v___f_1148_, 3, v_toConstantVal_1122_);
lean_closure_set(v___f_1148_, 4, v_numParams_1123_);
lean_closure_set(v___f_1148_, 5, v___x_1124_);
lean_closure_set(v___f_1148_, 6, v_n_1125_);
lean_closure_set(v___f_1148_, 7, v_levelParams_1126_);
lean_closure_set(v___f_1148_, 8, v___x_1147_);
lean_closure_set(v___f_1148_, 9, v_ctorType_1129_);
v___x_1154_ = lean_array_get_size(v_params_1128_);
v___x_1155_ = lean_nat_dec_eq(v___x_1154_, v_numParams_1123_);
lean_dec(v_numParams_1123_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec_ref(v___f_1148_);
lean_dec_ref(v_params_1128_);
lean_dec(v___x_1124_);
v___x_1156_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1157_ = l_Lean_MessageData_ofConstName(v_n_1125_, v___x_1155_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1160_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1161_;
}
else
{
goto v___jp_1149_;
}
v___jp_1135_:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1144_ = 0;
v___x_1145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1143_, v___y_1142_, v___y_1140_, v___y_1136_, v___x_1144_, v___y_1139_, v___y_1137_, v___y_1138_, v___y_1141_);
return v___x_1145_;
}
v___jp_1149_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Lean_Expr_const___override(v_n_1125_, v___x_1124_);
v___x_1151_ = l_Lean_mkAppN(v___x_1150_, v_params_1128_);
lean_dec_ref(v_params_1128_);
if (v_instImplicit_1120_ == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = 0;
v___y_1136_ = v___f_1148_;
v___y_1137_ = v___y_1131_;
v___y_1138_ = v___y_1132_;
v___y_1139_ = v___y_1130_;
v___y_1140_ = v___x_1151_;
v___y_1141_ = v___y_1133_;
v___y_1142_ = v___x_1152_;
goto v___jp_1135_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = 3;
v___y_1136_ = v___f_1148_;
v___y_1137_ = v___y_1131_;
v___y_1138_ = v___y_1132_;
v___y_1139_ = v___y_1130_;
v___y_1140_ = v___x_1151_;
v___y_1141_ = v___y_1133_;
v___y_1142_ = v___x_1153_;
goto v___jp_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1162_, lean_object* v_projDecls_1163_, lean_object* v_toConstantVal_1164_, lean_object* v_numParams_1165_, lean_object* v___x_1166_, lean_object* v_n_1167_, lean_object* v_levelParams_1168_, lean_object* v_a_1169_, lean_object* v_params_1170_, lean_object* v_ctorType_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_instImplicit_boxed_1177_; uint8_t v_a_18136__boxed_1178_; lean_object* v_res_1179_; 
v_instImplicit_boxed_1177_ = lean_unbox(v_instImplicit_1162_);
v_a_18136__boxed_1178_ = lean_unbox(v_a_1169_);
v_res_1179_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1177_, v_projDecls_1163_, v_toConstantVal_1164_, v_numParams_1165_, v___x_1166_, v_n_1167_, v_levelParams_1168_, v_a_18136__boxed_1178_, v_params_1170_, v_ctorType_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
if (lean_obj_tag(v_a_1180_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = l_List_reverse___redArg(v_a_1181_);
return v___x_1182_;
}
else
{
lean_object* v_head_1183_; lean_object* v_tail_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1193_; 
v_head_1183_ = lean_ctor_get(v_a_1180_, 0);
v_tail_1184_ = lean_ctor_get(v_a_1180_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1186_ = v_a_1180_;
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_tail_1184_);
lean_inc(v_head_1183_);
lean_dec(v_a_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = l_Lean_mkLevelParam(v_head_1183_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v_a_1181_);
lean_ctor_set(v___x_1186_, 0, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1181_);
v___x_1190_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_a_1180_ = v_tail_1184_;
v_a_1181_ = v___x_1190_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_instMonadEIO___redArg();
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_toApplicative_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1268_; 
v___x_1205_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1206_ = l_StateRefT_x27_instMonad___redArg(v___x_1205_);
v_toApplicative_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1206_, 1);
lean_dec(v_unused_1269_);
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1268_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_toApplicative_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1268_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_toFunctor_1211_; lean_object* v_toSeq_1212_; lean_object* v_toSeqLeft_1213_; lean_object* v_toSeqRight_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1266_; 
v_toFunctor_1211_ = lean_ctor_get(v_toApplicative_1207_, 0);
v_toSeq_1212_ = lean_ctor_get(v_toApplicative_1207_, 2);
v_toSeqLeft_1213_ = lean_ctor_get(v_toApplicative_1207_, 3);
v_toSeqRight_1214_ = lean_ctor_get(v_toApplicative_1207_, 4);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_toApplicative_1207_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_dec(v_unused_1267_);
v___x_1216_ = v_toApplicative_1207_;
v_isShared_1217_ = v_isSharedCheck_1266_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_toSeqRight_1214_);
lean_inc(v_toSeqLeft_1213_);
lean_inc(v_toSeq_1212_);
lean_inc(v_toFunctor_1211_);
lean_dec(v_toApplicative_1207_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1266_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; lean_object* v___x_1227_; 
v___f_1218_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1219_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1211_);
v___f_1220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1220_, 0, v_toFunctor_1211_);
v___f_1221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1221_, 0, v_toFunctor_1211_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___f_1220_);
lean_ctor_set(v___x_1222_, 1, v___f_1221_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toSeqRight_1214_);
v___f_1224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1224_, 0, v_toSeqLeft_1213_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toSeq_1212_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 4, v___f_1223_);
lean_ctor_set(v___x_1216_, 3, v___f_1224_);
lean_ctor_set(v___x_1216_, 2, v___f_1225_);
lean_ctor_set(v___x_1216_, 1, v___f_1218_);
lean_ctor_set(v___x_1216_, 0, v___x_1222_);
v___x_1227_ = v___x_1216_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___f_1218_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v___f_1225_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v___f_1224_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v___f_1223_);
v___x_1227_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___f_1219_);
lean_ctor_set(v___x_1209_, 0, v___x_1227_);
v___x_1229_ = v___x_1209_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___f_1219_);
v___x_1229_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; lean_object* v_toApplicative_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1262_; 
v___x_1230_ = l_StateRefT_x27_instMonad___redArg(v___x_1229_);
v_toApplicative_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1230_, 1);
lean_dec(v_unused_1263_);
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_toApplicative_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1262_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_toFunctor_1235_; lean_object* v_toSeq_1236_; lean_object* v_toSeqLeft_1237_; lean_object* v_toSeqRight_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1260_; 
v_toFunctor_1235_ = lean_ctor_get(v_toApplicative_1231_, 0);
v_toSeq_1236_ = lean_ctor_get(v_toApplicative_1231_, 2);
v_toSeqLeft_1237_ = lean_ctor_get(v_toApplicative_1231_, 3);
v_toSeqRight_1238_ = lean_ctor_get(v_toApplicative_1231_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_toApplicative_1231_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_toApplicative_1231_, 1);
lean_dec(v_unused_1261_);
v___x_1240_ = v_toApplicative_1231_;
v_isShared_1241_ = v_isSharedCheck_1260_;
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
v_isShared_1241_ = v_isSharedCheck_1260_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___f_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1251_; 
v___f_1242_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1243_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v___f_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v___f_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v___f_1247_);
v___x_1251_ = v_reuseFailAlloc_1259_;
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
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___f_1243_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_13115__overap_1256_; lean_object* v___x_1257_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = l_instInhabitedOfMonad___redArg(v___x_1253_, v___x_1254_);
v___x_13115__overap_1256_ = lean_panic_fn_borrowed(v___x_1255_, v_msg_1199_);
lean_dec(v___x_1255_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1257_ = lean_apply_5(v___x_13115__overap_1256_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, lean_box(0));
return v___x_1257_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1276_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1283_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1284_ = lean_unsigned_to_nat(11u);
v___x_1285_ = lean_unsigned_to_nat(122u);
v___x_1286_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1287_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1288_ = l_mkPanicMessageWithDecl(v___x_1287_, v___x_1286_, v___x_1285_, v___x_1284_, v___x_1283_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1303_; lean_object* v_env_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = lean_st_ref_get(v___y_1293_);
v_env_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_env_1304_);
lean_dec(v___x_1303_);
v___x_1305_ = 0;
lean_inc(v_constName_1289_);
v___x_1306_ = l_Lean_Environment_findAsync_x3f(v_env_1304_, v_constName_1289_, v___x_1305_);
if (lean_obj_tag(v___x_1306_) == 1)
{
lean_object* v_val_1307_; uint8_t v_kind_1308_; 
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v_kind_1308_ = lean_ctor_get_uint8(v_val_1307_, sizeof(void*)*3);
if (v_kind_1308_ == 6)
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1307_);
if (lean_obj_tag(v___x_1309_) == 6)
{
lean_object* v_val_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_constName_1289_);
v_val_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_val_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 0);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_val_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v___x_1309_);
v___x_1318_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1319_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1318_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
if (lean_obj_tag(v_a_1320_) == 0)
{
lean_del_object(v___x_1322_);
goto v___jp_1295_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1326_; 
lean_dec(v_constName_1289_);
v_val_1324_ = lean_ctor_get(v_a_1320_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v_a_1320_, 1);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_val_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_val_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_constName_1289_);
v_a_1329_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1319_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
else
{
lean_dec(v_val_1307_);
goto v___jp_1295_;
}
}
else
{
lean_dec(v___x_1306_);
goto v___jp_1295_;
}
v___jp_1295_:
{
lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1296_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1297_ = 0;
v___x_1298_ = l_Lean_MessageData_ofConstName(v_constName_1289_, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1296_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1301_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v_env_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_st_ref_get(v___y_1351_);
v_env_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc_ref(v_env_1354_);
lean_dec(v___x_1353_);
lean_inc(v_constName_1347_);
v___x_1355_ = l_Lean_isInductiveCore_x3f(v_env_1354_, v_constName_1347_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1356_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1357_ = 0;
v___x_1358_ = l_Lean_MessageData_ofConstName(v_constName_1347_, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1356_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1361_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1362_;
}
else
{
lean_object* v_val_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_constName_1347_);
v_val_1363_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1355_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_val_1363_);
lean_dec(v___x_1355_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 0);
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_val_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1377_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1384_, lean_object* v___x_1385_, uint8_t v_instImplicit_1386_, lean_object* v_projDecls_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
lean_inc(v_n_1384_);
v___x_1393_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1384_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1435_ = l_Lean_InductiveVal_numCtors(v_a_1394_);
v___x_1436_ = lean_unsigned_to_nat(1u);
v___x_1437_ = lean_nat_dec_eq(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec(v_a_1394_);
lean_dec_ref(v_projDecls_1387_);
v___x_1438_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1439_ = l_Lean_MessageData_ofConstName(v_n_1384_, v___x_1437_);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1442_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
return v___x_1443_;
}
else
{
v___y_1396_ = v___y_1388_;
v___y_1397_ = v___y_1389_;
v___y_1398_ = v___y_1390_;
v___y_1399_ = v___y_1391_;
goto v___jp_1395_;
}
v___jp_1395_:
{
lean_object* v_toConstantVal_1400_; lean_object* v_numParams_1401_; lean_object* v_ctors_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_toConstantVal_1400_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref(v_toConstantVal_1400_);
v_numParams_1401_ = lean_ctor_get(v_a_1394_, 1);
lean_inc(v_numParams_1401_);
v_ctors_1402_ = lean_ctor_get(v_a_1394_, 4);
lean_inc(v_ctors_1402_);
lean_dec(v_a_1394_);
v___x_1403_ = l_List_head_x21___redArg(v___x_1385_, v_ctors_1402_);
lean_dec(v_ctors_1402_);
v___x_1404_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1403_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_levelParams_1406_; lean_object* v_type_1407_; lean_object* v___x_1408_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v_levelParams_1406_ = lean_ctor_get(v_toConstantVal_1400_, 1);
lean_inc(v_levelParams_1406_);
v_type_1407_ = lean_ctor_get(v_toConstantVal_1400_, 2);
lean_inc_ref(v_type_1407_);
lean_dec_ref(v_toConstantVal_1400_);
v___x_1408_ = l_Lean_Meta_isPropFormerType(v_type_1407_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_toConstantVal_1409_; lean_object* v_a_1410_; lean_object* v_type_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v_toConstantVal_1409_ = lean_ctor_get(v_a_1405_, 0);
lean_inc_ref(v_toConstantVal_1409_);
lean_dec(v_a_1405_);
v_a_1410_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1408_, 1);
v_type_1411_ = lean_ctor_get(v_toConstantVal_1409_, 2);
lean_inc_ref(v_type_1411_);
v___x_1412_ = lean_box(0);
lean_inc(v_levelParams_1406_);
v___x_1413_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1406_, v___x_1412_);
v___x_1414_ = lean_box(v_instImplicit_1386_);
lean_inc(v_numParams_1401_);
v___f_1415_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1415_, 0, v___x_1414_);
lean_closure_set(v___f_1415_, 1, v_projDecls_1387_);
lean_closure_set(v___f_1415_, 2, v_toConstantVal_1409_);
lean_closure_set(v___f_1415_, 3, v_numParams_1401_);
lean_closure_set(v___f_1415_, 4, v___x_1413_);
lean_closure_set(v___f_1415_, 5, v_n_1384_);
lean_closure_set(v___f_1415_, 6, v_levelParams_1406_);
lean_closure_set(v___f_1415_, 7, v_a_1410_);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_numParams_1401_);
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1411_, v___x_1416_, v___f_1415_, v___x_1417_, v___x_1417_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1418_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec(v_levelParams_1406_);
lean_dec(v_a_1405_);
lean_dec(v_numParams_1401_);
lean_dec_ref(v_projDecls_1387_);
lean_dec(v_n_1384_);
v_a_1419_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1408_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1408_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec(v_numParams_1401_);
lean_dec_ref(v_toConstantVal_1400_);
lean_dec_ref(v_projDecls_1387_);
lean_dec(v_n_1384_);
v_a_1427_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1404_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1404_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_projDecls_1387_);
lean_dec(v_n_1384_);
v_a_1444_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1393_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1393_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1452_, lean_object* v___x_1453_, lean_object* v_instImplicit_1454_, lean_object* v_projDecls_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_instImplicit_boxed_1461_; lean_object* v_res_1462_; 
v_instImplicit_boxed_1461_ = lean_unbox(v_instImplicit_1454_);
v_res_1462_ = l_Lean_Meta_mkProjections___lam__2(v_n_1452_, v___x_1453_, v_instImplicit_boxed_1461_, v_projDecls_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___x_1453_);
return v_res_1462_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_unsigned_to_nat(32u);
v___x_1466_ = lean_mk_empty_array_with_capacity(v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1468_ = ((size_t)5ULL);
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_unsigned_to_nat(32u);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1470_);
v___x_1472_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
lean_ctor_set(v___x_1473_, 2, v___x_1469_);
lean_ctor_set(v___x_1473_, 3, v___x_1469_);
lean_ctor_set_usize(v___x_1473_, 4, v___x_1468_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_box(1);
v___x_1475_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1476_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
lean_ctor_set(v___x_1477_, 2, v___x_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1480_, lean_object* v_projDecls_1481_, uint8_t v_instImplicit_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_box(v_instImplicit_1482_);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1490_, 0, v_n_1480_);
lean_closure_set(v___f_1490_, 1, v___x_1488_);
lean_closure_set(v___f_1490_, 2, v___x_1489_);
lean_closure_set(v___f_1490_, 3, v_projDecls_1481_);
v___x_1491_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1492_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1493_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1491_, v___x_1492_, v___f_1490_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1494_, lean_object* v_projDecls_1495_, lean_object* v_instImplicit_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
uint8_t v_instImplicit_boxed_1502_; lean_object* v_res_1503_; 
v_instImplicit_boxed_1502_ = lean_unbox(v_instImplicit_1496_);
v_res_1503_ = l_Lean_Meta_mkProjections(v_n_1494_, v_projDecls_1495_, v_instImplicit_boxed_1502_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1504_, lean_object* v_as_1505_, size_t v_sz_1506_, size_t v_i_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1504_, v_as_1505_, v_sz_1506_, v_i_1507_, v_b_1508_, v___y_1509_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1515_, lean_object* v_as_1516_, lean_object* v_sz_1517_, lean_object* v_i_1518_, lean_object* v_b_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v_instImplicit_boxed_1525_; size_t v_sz_boxed_1526_; size_t v_i_boxed_1527_; lean_object* v_res_1528_; 
v_instImplicit_boxed_1525_ = lean_unbox(v_instImplicit_1515_);
v_sz_boxed_1526_ = lean_unbox_usize(v_sz_1517_);
lean_dec(v_sz_1517_);
v_i_boxed_1527_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1525_, v_as_1516_, v_sz_boxed_1526_, v_i_boxed_1527_, v_b_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec_ref(v_as_1516_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1529_, uint8_t v_s_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1529_, v_s_1530_, v___y_1532_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1537_, lean_object* v_s_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v_s_boxed_1544_; lean_object* v_res_1545_; 
v_s_boxed_1544_ = lean_unbox(v_s_1538_);
v_res_1545_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1537_, v_s_boxed_1544_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1546_, lean_object* v_ref_1547_, lean_object* v_msg_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1547_, v_msg_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_ref_1556_, lean_object* v_msg_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1555_, v_ref_1556_, v_msg_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v_ref_1556_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1564_, lean_object* v_x_1565_, uint8_t v_isExporting_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1565_, v_isExporting_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_x_1574_, lean_object* v_isExporting_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_isExporting_boxed_1581_; lean_object* v_res_1582_; 
v_isExporting_boxed_1581_ = lean_unbox(v_isExporting_1575_);
v_res_1582_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1573_, v_x_1574_, v_isExporting_boxed_1581_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1583_, lean_object* v_x_1584_, uint8_t v_when_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1584_, v_when_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_x_1593_, lean_object* v_when_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v_when_boxed_1600_; lean_object* v_res_1601_; 
v_when_boxed_1600_ = lean_unbox(v_when_1594_);
v_res_1601_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1592_, v_x_1593_, v_when_boxed_1600_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1602_, lean_object* v_projDecls_1603_, lean_object* v___x_1604_, lean_object* v___x_1605_, uint8_t v_instImplicit_1606_, lean_object* v___x_1607_, lean_object* v_params_1608_, lean_object* v_self_1609_, lean_object* v_a_1610_, lean_object* v___x_1611_, lean_object* v_n_1612_, lean_object* v___x_1613_, uint8_t v_a_1614_, lean_object* v_inst_1615_, lean_object* v_R_1616_, lean_object* v_a_1617_, lean_object* v_b_1618_, lean_object* v_c_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1602_, v_projDecls_1603_, v___x_1604_, v___x_1605_, v_instImplicit_1606_, v___x_1607_, v_params_1608_, v_self_1609_, v_a_1610_, v___x_1611_, v_n_1612_, v___x_1613_, v_a_1614_, v_a_1617_, v_b_1618_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1626_ = _args[0];
lean_object* v_projDecls_1627_ = _args[1];
lean_object* v___x_1628_ = _args[2];
lean_object* v___x_1629_ = _args[3];
lean_object* v_instImplicit_1630_ = _args[4];
lean_object* v___x_1631_ = _args[5];
lean_object* v_params_1632_ = _args[6];
lean_object* v_self_1633_ = _args[7];
lean_object* v_a_1634_ = _args[8];
lean_object* v___x_1635_ = _args[9];
lean_object* v_n_1636_ = _args[10];
lean_object* v___x_1637_ = _args[11];
lean_object* v_a_1638_ = _args[12];
lean_object* v_inst_1639_ = _args[13];
lean_object* v_R_1640_ = _args[14];
lean_object* v_a_1641_ = _args[15];
lean_object* v_b_1642_ = _args[16];
lean_object* v_c_1643_ = _args[17];
lean_object* v___y_1644_ = _args[18];
lean_object* v___y_1645_ = _args[19];
lean_object* v___y_1646_ = _args[20];
lean_object* v___y_1647_ = _args[21];
lean_object* v___y_1648_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1649_; uint8_t v_a_18887__boxed_1650_; lean_object* v_res_1651_; 
v_instImplicit_boxed_1649_ = lean_unbox(v_instImplicit_1630_);
v_a_18887__boxed_1650_ = lean_unbox(v_a_1638_);
v_res_1651_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1626_, v_projDecls_1627_, v___x_1628_, v___x_1629_, v_instImplicit_boxed_1649_, v___x_1631_, v_params_1632_, v_self_1633_, v_a_1634_, v___x_1635_, v_n_1636_, v___x_1637_, v_a_18887__boxed_1650_, v_inst_1639_, v_R_1640_, v_a_1641_, v_b_1642_, v_c_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_projDecls_1627_);
lean_dec(v_upperBound_1626_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1652_, uint8_t v_allowLevelAssignments_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1653_, v_k_1652_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1659_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1659_);
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
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1676_, lean_object* v_allowLevelAssignments_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1683_; lean_object* v_res_1684_; 
v_allowLevelAssignments_boxed_1683_ = lean_unbox(v_allowLevelAssignments_1677_);
v_res_1684_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1676_, v_allowLevelAssignments_boxed_1683_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1685_, lean_object* v_k_1686_, uint8_t v_allowLevelAssignments_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1686_, v_allowLevelAssignments_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_k_1695_, lean_object* v_allowLevelAssignments_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1702_; lean_object* v_res_1703_; 
v_allowLevelAssignments_boxed_1702_ = lean_unbox(v_allowLevelAssignments_1696_);
v_res_1703_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1694_, v_k_1695_, v_allowLevelAssignments_boxed_1702_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1707_);
return v___x_1714_;
}
else
{
lean_object* v_snd_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1770_; 
v_snd_1715_ = lean_ctor_get(v_b_1707_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_b_1707_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v_b_1707_, 0);
lean_dec(v_unused_1771_);
v___x_1717_ = v_b_1707_;
v_isShared_1718_ = v_isSharedCheck_1770_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_snd_1715_);
lean_dec(v_b_1707_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1770_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_array_1719_; lean_object* v_start_1720_; lean_object* v_stop_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_array_1719_ = lean_ctor_get(v_snd_1715_, 0);
v_start_1720_ = lean_ctor_get(v_snd_1715_, 1);
v_stop_1721_ = lean_ctor_get(v_snd_1715_, 2);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_nat_dec_lt(v_start_1720_, v_stop_1721_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1725_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1722_);
v___x_1725_ = v___x_1717_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_snd_1715_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
else
{
lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1766_; 
lean_inc(v_stop_1721_);
lean_inc(v_start_1720_);
lean_inc_ref(v_array_1719_);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_snd_1715_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; lean_object* v_unused_1768_; lean_object* v_unused_1769_; 
v_unused_1767_ = lean_ctor_get(v_snd_1715_, 2);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_snd_1715_, 1);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_snd_1715_, 0);
lean_dec(v_unused_1769_);
v___x_1729_ = v_snd_1715_;
v_isShared_1730_ = v_isSharedCheck_1766_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v_snd_1715_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1766_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v_a_1731_ = lean_array_uget_borrowed(v_as_1704_, v_i_1706_);
v___x_1732_ = lean_array_fget(v_array_1719_, v_start_1720_);
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_start_1720_, v___x_1733_);
lean_dec(v_start_1720_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v___x_1734_);
v___x_1736_ = v___x_1729_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_array_1719_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_stop_1721_);
v___x_1736_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; 
lean_inc(v_a_1731_);
v___x_1737_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1731_, v___x_1732_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1756_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_unbox(v_a_1738_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1738_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1736_);
lean_ctor_set(v___x_1717_, 0, v___x_1743_);
v___x_1745_ = v___x_1717_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1736_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1745_);
v___x_1747_ = v___x_1740_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
lean_object* v___x_1751_; 
lean_del_object(v___x_1740_);
lean_dec(v_a_1738_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1736_);
lean_ctor_set(v___x_1717_, 0, v___x_1722_);
v___x_1751_ = v___x_1717_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1736_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
size_t v___x_1752_; size_t v___x_1753_; 
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1706_, v___x_1752_);
v_i_1706_ = v___x_1753_;
v_b_1707_ = v___x_1751_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___x_1736_);
lean_del_object(v___x_1717_);
v_a_1757_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1737_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1737_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1772_, lean_object* v_sz_1773_, lean_object* v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
size_t v_sz_boxed_1781_; size_t v_i_boxed_1782_; lean_object* v_res_1783_; 
v_sz_boxed_1781_ = lean_unbox_usize(v_sz_1773_);
lean_dec(v_sz_1773_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1772_, v_sz_boxed_1781_, v_i_boxed_1782_, v_b_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v_as_1772_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1784_, lean_object* v_params2_1785_, lean_object* v___x_1786_, lean_object* v_params1_1787_, uint8_t v___x_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
if (v___x_1784_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec(v___x_1786_);
lean_dec_ref(v_params2_1785_);
v___x_1794_ = lean_box(v___x_1784_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; size_t v_sz_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = l_Array_toSubarray___redArg(v_params2_1785_, v___x_1796_, v___x_1786_);
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v___x_1797_);
v_sz_1800_ = lean_array_size(v_params1_1787_);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1787_, v_sz_1800_, v___x_1801_, v___x_1799_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1816_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1816_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_fst_1807_; 
v_fst_1807_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_fst_1807_);
lean_dec(v_a_1803_);
if (lean_obj_tag(v_fst_1807_) == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_box(v___x_1788_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1814_; 
v_val_1812_ = lean_ctor_get(v_fst_1807_, 0);
lean_inc(v_val_1812_);
lean_dec_ref_known(v_fst_1807_, 1);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v_val_1812_);
v___x_1814_ = v___x_1805_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_val_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1802_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1802_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1825_, lean_object* v_params2_1826_, lean_object* v___x_1827_, lean_object* v_params1_1828_, lean_object* v___x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
uint8_t v___x_2007__boxed_1835_; uint8_t v___x_2009__boxed_1836_; lean_object* v_res_1837_; 
v___x_2007__boxed_1835_ = lean_unbox(v___x_1825_);
v___x_2009__boxed_1836_ = lean_unbox(v___x_1829_);
v_res_1837_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1835_, v_params2_1826_, v___x_1827_, v_params1_1828_, v___x_2009__boxed_1836_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec_ref(v_params1_1828_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1838_, lean_object* v_params2_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___y_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; 
v___x_1845_ = lean_array_get_size(v_params1_1838_);
v___x_1846_ = lean_array_get_size(v_params2_1839_);
v___x_1847_ = lean_nat_dec_eq(v___x_1845_, v___x_1846_);
v___x_1848_ = 1;
v___x_1849_ = lean_box(v___x_1847_);
v___x_1850_ = lean_box(v___x_1848_);
v___y_1851_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1851_, 0, v___x_1849_);
lean_closure_set(v___y_1851_, 1, v_params2_1839_);
lean_closure_set(v___y_1851_, 2, v___x_1846_);
lean_closure_set(v___y_1851_, 3, v_params1_1838_);
lean_closure_set(v___y_1851_, 4, v___x_1850_);
v___x_1852_ = 0;
v___x_1853_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1851_, v___x_1852_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1854_, lean_object* v_params2_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1854_, v_params2_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_env_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = lean_st_ref_get(v___y_1863_);
v_env_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_ref(v_env_1866_);
lean_dec(v___x_1865_);
v___x_1867_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1866_, v_declName_1862_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1869_, v___y_1870_);
lean_dec(v___y_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1873_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1887_; lean_object* v_dummy_1888_; 
v___x_1887_ = lean_box(0);
v_dummy_1888_ = l_Lean_Expr_sort___override(v___x_1887_);
return v_dummy_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1889_, lean_object* v_induct_1890_, lean_object* v_params_1891_, lean_object* v_idx_1892_, lean_object* v_e_1893_, lean_object* v_x_x3f_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
if (lean_obj_tag(v_e_1893_) == 11)
{
lean_object* v_typeName_1906_; lean_object* v_idx_1907_; lean_object* v_struct_1908_; uint8_t v___x_1955_; 
v_typeName_1906_ = lean_ctor_get(v_e_1893_, 0);
v_idx_1907_ = lean_ctor_get(v_e_1893_, 1);
v_struct_1908_ = lean_ctor_get(v_e_1893_, 2);
lean_inc_ref(v_struct_1908_);
v___x_1955_ = lean_nat_dec_eq(v_idx_1907_, v_idx_1892_);
if (v___x_1955_ == 0)
{
lean_dec_ref(v_struct_1908_);
lean_dec_ref_known(v_e_1893_, 3);
lean_dec_ref(v_params_1891_);
goto v___jp_1900_;
}
else
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_name_eq(v_induct_1890_, v_typeName_1906_);
if (v___x_1956_ == 0)
{
lean_dec_ref(v_struct_1908_);
lean_dec_ref_known(v_e_1893_, 3);
lean_dec_ref(v_params_1891_);
goto v___jp_1900_;
}
else
{
if (lean_obj_tag(v_x_x3f_1894_) == 0)
{
goto v___jp_1909_;
}
else
{
lean_object* v_val_1957_; uint8_t v___x_1958_; 
v_val_1957_ = lean_ctor_get(v_x_x3f_1894_, 0);
v___x_1958_ = lean_expr_eqv(v_val_1957_, v_struct_1908_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_struct_1908_);
lean_dec_ref_known(v_e_1893_, 3);
lean_dec_ref(v_params_1891_);
goto v___jp_1900_;
}
else
{
goto v___jp_1909_;
}
}
}
}
v___jp_1909_:
{
lean_object* v___x_1910_; 
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
lean_inc(v_a_1896_);
lean_inc_ref(v_a_1895_);
v___x_1910_ = lean_infer_type(v_e_1893_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
lean_inc(v_a_1896_);
lean_inc_ref(v_a_1895_);
v___x_1912_ = lean_whnf(v_a_1911_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v_dummy_1914_; lean_object* v_nargs_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v_dummy_1914_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1915_ = l_Lean_Expr_getAppNumArgs(v_a_1913_);
lean_inc(v_nargs_1915_);
v___x_1916_ = lean_mk_array(v_nargs_1915_, v_dummy_1914_);
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_sub(v_nargs_1915_, v___x_1917_);
lean_dec(v_nargs_1915_);
v___x_1919_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1913_, v___x_1916_, v___x_1918_);
v___x_1920_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1891_, v___x_1919_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1930_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_unbox(v_a_1921_);
lean_dec(v_a_1921_);
if (v___x_1925_ == 0)
{
lean_del_object(v___x_1923_);
lean_dec_ref(v_struct_1908_);
goto v___jp_1900_;
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_struct_1908_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1928_ = v___x_1923_;
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
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_struct_1908_);
v_a_1931_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1920_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1920_);
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
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_struct_1908_);
lean_dec_ref(v_params_1891_);
v_a_1939_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1912_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1912_);
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
lean_dec_ref(v_struct_1908_);
lean_dec_ref(v_params_1891_);
v_a_1947_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1910_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1910_);
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
}
else
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_Expr_getAppFn(v_e_1893_);
if (lean_obj_tag(v___x_1959_) == 4)
{
lean_object* v_declName_1960_; lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2011_; 
v_declName_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_declName_1960_);
lean_dec_ref_known(v___x_1959_, 2);
v___x_1961_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1960_, v_a_1898_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2011_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2011_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___y_1967_; lean_object* v___y_1968_; 
if (lean_obj_tag(v_a_1962_) == 1)
{
lean_object* v_val_1996_; lean_object* v_ctorName_1997_; lean_object* v_numParams_1998_; lean_object* v_i_1999_; uint8_t v___y_2001_; uint8_t v___x_2009_; 
v_val_1996_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v_a_1962_, 1);
v_ctorName_1997_ = lean_ctor_get(v_val_1996_, 0);
lean_inc(v_ctorName_1997_);
v_numParams_1998_ = lean_ctor_get(v_val_1996_, 1);
lean_inc(v_numParams_1998_);
v_i_1999_ = lean_ctor_get(v_val_1996_, 2);
lean_inc(v_i_1999_);
lean_dec(v_val_1996_);
v___x_2009_ = lean_name_eq(v_ctorName_1997_, v_ctor_1889_);
lean_dec(v_ctorName_1997_);
if (v___x_2009_ == 0)
{
lean_dec(v_i_1999_);
v___y_2001_ = v___x_2009_;
goto v___jp_2000_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_nat_dec_eq(v_i_1999_, v_idx_1892_);
lean_dec(v_i_1999_);
v___y_2001_ = v___x_2010_;
goto v___jp_2000_;
}
v___jp_2000_:
{
if (v___y_2001_ == 0)
{
lean_dec(v_numParams_1998_);
lean_del_object(v___x_1964_);
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_params_1891_);
goto v___jp_1903_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2002_ = l_Lean_Expr_getAppNumArgs(v_e_1893_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_numParams_1998_, v___x_2003_);
lean_dec(v_numParams_1998_);
v___x_2005_ = lean_nat_dec_eq(v___x_2002_, v___x_2004_);
lean_dec(v___x_2004_);
lean_dec(v___x_2002_);
if (v___x_2005_ == 0)
{
lean_del_object(v___x_1964_);
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_params_1891_);
goto v___jp_1903_;
}
else
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Expr_appArg_x21(v_e_1893_);
if (lean_obj_tag(v_x_x3f_1894_) == 0)
{
v___y_1967_ = v___x_2006_;
v___y_1968_ = v___x_2003_;
goto v___jp_1966_;
}
else
{
lean_object* v_val_2007_; uint8_t v___x_2008_; 
v_val_2007_ = lean_ctor_get(v_x_x3f_1894_, 0);
v___x_2008_ = lean_expr_eqv(v_val_2007_, v___x_2006_);
if (v___x_2008_ == 0)
{
lean_dec_ref(v___x_2006_);
lean_del_object(v___x_1964_);
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_params_1891_);
goto v___jp_1903_;
}
else
{
v___y_1967_ = v___x_2006_;
v___y_1968_ = v___x_2003_;
goto v___jp_1966_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1964_);
lean_dec(v_a_1962_);
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_params_1891_);
goto v___jp_1903_;
}
v___jp_1966_:
{
lean_object* v___x_1969_; lean_object* v_dummy_1970_; lean_object* v_nargs_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1969_ = l_Lean_Expr_appFn_x21(v_e_1893_);
lean_dec_ref(v_e_1893_);
v_dummy_1970_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1971_ = l_Lean_Expr_getAppNumArgs(v___x_1969_);
lean_inc(v_nargs_1971_);
v___x_1972_ = lean_mk_array(v_nargs_1971_, v_dummy_1970_);
v___x_1973_ = lean_nat_sub(v_nargs_1971_, v___y_1968_);
lean_dec(v_nargs_1971_);
v___x_1974_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1969_, v___x_1972_, v___x_1973_);
v___x_1975_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1891_, v___x_1974_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1987_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1987_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1987_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_unbox(v_a_1976_);
lean_dec(v_a_1976_);
if (v___x_1980_ == 0)
{
lean_del_object(v___x_1978_);
lean_dec_ref(v___y_1967_);
lean_del_object(v___x_1964_);
goto v___jp_1903_;
}
else
{
lean_object* v___x_1982_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 1);
lean_ctor_set(v___x_1964_, 0, v___y_1967_);
v___x_1982_ = v___x_1964_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___y_1967_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1982_);
v___x_1984_ = v___x_1978_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___y_1967_);
lean_del_object(v___x_1964_);
v_a_1988_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1975_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1975_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_e_1893_);
lean_dec_ref(v_params_1891_);
goto v___jp_1903_;
}
}
v___jp_1900_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
v___jp_1903_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2012_, lean_object* v_induct_2013_, lean_object* v_params_2014_, lean_object* v_idx_2015_, lean_object* v_e_2016_, lean_object* v_x_x3f_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2012_, v_induct_2013_, v_params_2014_, v_idx_2015_, v_e_2016_, v_x_x3f_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_x_x3f_2017_);
lean_dec(v_idx_2015_);
lean_dec(v_induct_2013_);
lean_dec(v_ctor_2012_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v_env_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
v___x_2030_ = lean_st_ref_get(v___y_2028_);
v_env_2034_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_env_2034_);
lean_dec(v___x_2030_);
v___x_2035_ = 0;
v___x_2036_ = l_Lean_Environment_findAsync_x3f(v_env_2034_, v_constName_2024_, v___x_2035_);
if (lean_obj_tag(v___x_2036_) == 1)
{
lean_object* v_val_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2056_; 
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2056_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_val_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2056_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
uint8_t v_kind_2041_; 
v_kind_2041_ = lean_ctor_get_uint8(v_val_2037_, sizeof(void*)*3);
if (v_kind_2041_ == 6)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2037_);
if (lean_obj_tag(v___x_2042_) == 6)
{
lean_object* v_val_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2053_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_val_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v_val_2043_);
v___x_2048_ = v___x_2039_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_val_2043_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2048_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref(v___x_2042_);
lean_del_object(v___x_2039_);
v___x_2054_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2055_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2054_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2055_;
}
}
else
{
lean_del_object(v___x_2039_);
lean_dec(v_val_2037_);
goto v___jp_2031_;
}
}
}
else
{
lean_dec(v___x_2036_);
goto v___jp_2031_;
}
v___jp_2031_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2072_, lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v_declName_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v_a_2078_, lean_object* v_val_2079_, lean_object* v_a_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_nat_dec_lt(v_a_2080_, v_upperBound_2072_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2077_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2081_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref(v_b_2081_);
v___x_2089_ = l_Lean_instInhabitedExpr;
v___x_2090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2091_ = lean_nat_add(v___x_2073_, v_a_2080_);
v___x_2092_ = lean_array_get_borrowed(v___x_2089_, v___x_2074_, v___x_2091_);
lean_dec(v___x_2091_);
lean_inc(v___x_2092_);
lean_inc_ref(v___x_2077_);
v___x_2093_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2075_, v___x_2076_, v___x_2077_, v_a_2080_, v___x_2092_, v_a_2078_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2111_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 1)
{
lean_object* v_val_2098_; uint8_t v___x_2099_; 
v_val_2098_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_val_2098_);
lean_dec_ref_known(v_a_2094_, 1);
v___x_2099_ = lean_expr_eqv(v_val_2098_, v_val_2079_);
lean_dec(v_val_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2077_);
v___x_2100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2096_);
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_add(v_a_2080_, v___x_2104_);
lean_dec(v_a_2080_);
v_a_2080_ = v___x_2105_;
v_b_2081_ = v___x_2090_;
goto _start;
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_a_2094_);
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2077_);
v___x_2107_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2107_);
v___x_2109_ = v___x_2096_;
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
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_a_2080_);
lean_dec_ref(v___x_2077_);
v_a_2112_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2093_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2093_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v_declName_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_a_2126_, lean_object* v_val_2127_, lean_object* v_a_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2120_, v___x_2121_, v___x_2122_, v_declName_2123_, v___x_2124_, v___x_2125_, v_a_2126_, v_val_2127_, v_a_2128_, v_b_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v_val_2127_);
lean_dec(v_a_2126_);
lean_dec(v___x_2124_);
lean_dec(v_declName_2123_);
lean_dec_ref(v___x_2122_);
lean_dec(v___x_2121_);
lean_dec(v_upperBound_2120_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2136_, lean_object* v_p_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Expr_getAppFn(v_e_2136_);
if (lean_obj_tag(v___x_2143_) == 4)
{
lean_object* v_declName_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_declName_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc_n(v_declName_2144_, 2);
lean_dec_ref_known(v___x_2143_, 2);
v___x_2145_ = l_Lean_instInhabitedExpr;
v___x_2146_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2144_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2218_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2218_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2218_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
if (lean_obj_tag(v_a_2147_) == 1)
{
lean_object* v_val_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2215_; 
v_val_2156_ = lean_ctor_get(v_a_2147_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2147_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2158_ = v_a_2147_;
v_isShared_2159_ = v_isSharedCheck_2215_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_val_2156_);
lean_dec(v_a_2147_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2215_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_induct_2160_; lean_object* v_numParams_2161_; lean_object* v_numFields_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_induct_2160_ = lean_ctor_get(v_val_2156_, 1);
lean_inc_n(v_induct_2160_, 2);
v_numParams_2161_ = lean_ctor_get(v_val_2156_, 3);
lean_inc(v_numParams_2161_);
v_numFields_2162_ = lean_ctor_get(v_val_2156_, 4);
lean_inc(v_numFields_2162_);
lean_dec(v_val_2156_);
v___x_2163_ = lean_apply_1(v_p_2137_, v_induct_2160_);
v___x_2164_ = lean_unbox(v___x_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec(v_numFields_2162_);
lean_dec(v_numParams_2161_);
lean_dec(v_induct_2160_);
lean_del_object(v___x_2149_);
lean_dec(v_declName_2144_);
lean_dec_ref(v_e_2136_);
v___x_2165_ = lean_box(0);
if (v_isShared_2159_ == 0)
{
lean_ctor_set_tag(v___x_2158_, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2165_);
v___x_2167_ = v___x_2158_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
lean_del_object(v___x_2158_);
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_nat_dec_lt(v___x_2169_, v_numFields_2162_);
if (v___x_2170_ == 0)
{
lean_dec(v_numFields_2162_);
lean_dec(v_numParams_2161_);
lean_dec(v_induct_2160_);
lean_dec(v_declName_2144_);
lean_dec_ref(v_e_2136_);
goto v___jp_2151_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2171_ = l_Lean_Expr_getAppNumArgs(v_e_2136_);
v___x_2172_ = lean_nat_add(v_numParams_2161_, v_numFields_2162_);
v___x_2173_ = lean_nat_dec_eq(v___x_2171_, v___x_2172_);
lean_dec(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_numFields_2162_);
lean_dec(v_numParams_2161_);
lean_dec(v_induct_2160_);
lean_dec(v_declName_2144_);
lean_dec_ref(v_e_2136_);
goto v___jp_2151_;
}
else
{
lean_object* v_dummy_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_del_object(v___x_2149_);
v_dummy_2174_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2171_);
v___x_2175_ = lean_mk_array(v___x_2171_, v_dummy_2174_);
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_sub(v___x_2171_, v___x_2176_);
lean_dec(v___x_2171_);
v___x_2178_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2136_, v___x_2175_, v___x_2177_);
lean_inc(v_numParams_2161_);
v___x_2179_ = l_Array_extract___redArg(v___x_2178_, v___x_2169_, v_numParams_2161_);
v___x_2180_ = lean_array_get(v___x_2145_, v___x_2178_, v_numParams_2161_);
v___x_2181_ = lean_box(0);
lean_inc_ref(v___x_2179_);
v___x_2182_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2144_, v_induct_2160_, v___x_2179_, v___x_2169_, v___x_2180_, v___x_2181_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2214_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2214_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2214_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
if (lean_obj_tag(v_a_2183_) == 1)
{
lean_object* v_val_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_del_object(v___x_2185_);
v_val_2187_ = lean_ctor_get(v_a_2183_, 0);
v___x_2188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2162_, v_numParams_2161_, v___x_2178_, v_declName_2144_, v_induct_2160_, v___x_2179_, v_a_2183_, v_val_2187_, v___x_2176_, v___x_2188_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_induct_2160_);
lean_dec(v_declName_2144_);
lean_dec_ref(v___x_2178_);
lean_dec(v_numParams_2161_);
lean_dec(v_numFields_2162_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2202_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2202_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v_fst_2194_; 
v_fst_2194_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_fst_2194_);
lean_dec(v_a_2190_);
if (lean_obj_tag(v_fst_2194_) == 0)
{
lean_object* v___x_2196_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_a_2183_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2183_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2200_; 
lean_dec_ref_known(v_a_2183_, 1);
v_val_2198_ = lean_ctor_get(v_fst_2194_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_fst_2194_, 1);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_val_2198_);
v___x_2200_ = v___x_2192_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_val_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref_known(v_a_2183_, 1);
v_a_2203_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2189_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2189_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
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
lean_object* v___x_2212_; 
lean_dec(v_a_2183_);
lean_dec_ref(v___x_2179_);
lean_dec_ref(v___x_2178_);
lean_dec(v_numFields_2162_);
lean_dec(v_numParams_2161_);
lean_dec(v_induct_2160_);
lean_dec(v_declName_2144_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2181_);
v___x_2212_ = v___x_2185_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2181_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_dec_ref(v___x_2179_);
lean_dec_ref(v___x_2178_);
lean_dec(v_numFields_2162_);
lean_dec(v_numParams_2161_);
lean_dec(v_induct_2160_);
lean_dec(v_declName_2144_);
return v___x_2182_;
}
}
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_del_object(v___x_2149_);
lean_dec(v_a_2147_);
lean_dec(v_declName_2144_);
lean_dec_ref(v_p_2137_);
lean_dec_ref(v_e_2136_);
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
v___jp_2151_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = lean_box(0);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2152_);
v___x_2154_ = v___x_2149_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_declName_2144_);
lean_dec_ref(v_p_2137_);
lean_dec_ref(v_e_2136_);
v_a_2219_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2146_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2146_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
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
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_p_2137_);
lean_dec_ref(v_e_2136_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2229_, lean_object* v_p_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Meta_etaStruct_x3f(v_e_2229_, v_p_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2237_, lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_declName_2240_, lean_object* v___x_2241_, lean_object* v___x_2242_, lean_object* v_a_2243_, lean_object* v_val_2244_, lean_object* v_inst_2245_, lean_object* v_R_2246_, lean_object* v_a_2247_, lean_object* v_b_2248_, lean_object* v_c_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2237_, v___x_2238_, v___x_2239_, v_declName_2240_, v___x_2241_, v___x_2242_, v_a_2243_, v_val_2244_, v_a_2247_, v_b_2248_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2256_ = _args[0];
lean_object* v___x_2257_ = _args[1];
lean_object* v___x_2258_ = _args[2];
lean_object* v_declName_2259_ = _args[3];
lean_object* v___x_2260_ = _args[4];
lean_object* v___x_2261_ = _args[5];
lean_object* v_a_2262_ = _args[6];
lean_object* v_val_2263_ = _args[7];
lean_object* v_inst_2264_ = _args[8];
lean_object* v_R_2265_ = _args[9];
lean_object* v_a_2266_ = _args[10];
lean_object* v_b_2267_ = _args[11];
lean_object* v_c_2268_ = _args[12];
lean_object* v___y_2269_ = _args[13];
lean_object* v___y_2270_ = _args[14];
lean_object* v___y_2271_ = _args[15];
lean_object* v___y_2272_ = _args[16];
lean_object* v___y_2273_ = _args[17];
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2256_, v___x_2257_, v___x_2258_, v_declName_2259_, v___x_2260_, v___x_2261_, v_a_2262_, v_val_2263_, v_inst_2264_, v_R_2265_, v_a_2266_, v_b_2267_, v_c_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_val_2263_);
lean_dec(v_a_2262_);
lean_dec(v___x_2260_);
lean_dec(v_declName_2259_);
lean_dec_ref(v___x_2258_);
lean_dec(v___x_2257_);
lean_dec(v_upperBound_2256_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = l_Lean_Expr_hasMVar(v_e_2275_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_e_2275_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v_mctx_2281_; lean_object* v___x_2282_; lean_object* v_fst_2283_; lean_object* v_snd_2284_; lean_object* v___x_2285_; lean_object* v_cache_2286_; lean_object* v_zetaDeltaFVarIds_2287_; lean_object* v_postponed_2288_; lean_object* v_diag_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
v___x_2280_ = lean_st_ref_get(v___y_2276_);
v_mctx_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_mctx_2281_);
lean_dec(v___x_2280_);
v___x_2282_ = l_Lean_instantiateMVarsCore(v_mctx_2281_, v_e_2275_);
v_fst_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_fst_2283_);
v_snd_2284_ = lean_ctor_get(v___x_2282_, 1);
lean_inc(v_snd_2284_);
lean_dec_ref(v___x_2282_);
v___x_2285_ = lean_st_ref_take(v___y_2276_);
v_cache_2286_ = lean_ctor_get(v___x_2285_, 1);
v_zetaDeltaFVarIds_2287_ = lean_ctor_get(v___x_2285_, 2);
v_postponed_2288_ = lean_ctor_get(v___x_2285_, 3);
v_diag_2289_ = lean_ctor_get(v___x_2285_, 4);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v___x_2285_, 0);
lean_dec(v_unused_2299_);
v___x_2291_ = v___x_2285_;
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_diag_2289_);
lean_inc(v_postponed_2288_);
lean_inc(v_zetaDeltaFVarIds_2287_);
lean_inc(v_cache_2286_);
lean_dec(v___x_2285_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_snd_2284_);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_snd_2284_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_cache_2286_);
lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_zetaDeltaFVarIds_2287_);
lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_postponed_2288_);
lean_ctor_set(v_reuseFailAlloc_2297_, 4, v_diag_2289_);
v___x_2294_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_st_ref_put(v___y_2276_, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_fst_2283_);
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2300_, v___y_2301_);
lean_dec(v___y_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2304_, v___y_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_x_2328_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2335_, lean_object* v_e_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Meta_etaStruct_x3f(v_e_2336_, v_p_2335_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2362_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2362_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2362_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
if (lean_obj_tag(v_a_2343_) == 1)
{
lean_object* v_val_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2357_; 
v_val_2347_ = lean_ctor_get(v_a_2343_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2349_ = v_a_2343_;
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_val_2347_);
lean_dec(v_a_2343_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 0);
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_val_2347_);
v___x_2352_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2352_);
v___x_2354_ = v___x_2345_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
lean_dec(v_a_2343_);
v___x_2358_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2358_);
v___x_2360_ = v___x_2345_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2342_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2342_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2371_, lean_object* v_e_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2371_, v_e_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2379_, lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_apply_1(v_x_2380_, lean_box(0));
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2388_, v_x_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2396_, lean_object* v_b_2397_, lean_object* v_x_2398_){
_start:
{
if (lean_obj_tag(v_x_2398_) == 0)
{
lean_dec(v_b_2397_);
lean_dec_ref(v_a_2396_);
return v_x_2398_;
}
else
{
lean_object* v_key_2399_; lean_object* v_value_2400_; lean_object* v_tail_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2413_; 
v_key_2399_ = lean_ctor_get(v_x_2398_, 0);
v_value_2400_ = lean_ctor_get(v_x_2398_, 1);
v_tail_2401_ = lean_ctor_get(v_x_2398_, 2);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_x_2398_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2403_ = v_x_2398_;
v_isShared_2404_ = v_isSharedCheck_2413_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_tail_2401_);
lean_inc(v_value_2400_);
lean_inc(v_key_2399_);
lean_dec(v_x_2398_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2413_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Lean_ExprStructEq_beq(v_key_2399_, v_a_2396_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2396_, v_b_2397_, v_tail_2401_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 2, v___x_2406_);
v___x_2408_ = v___x_2403_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_key_2399_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_value_2400_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
else
{
lean_object* v___x_2411_; 
lean_dec(v_value_2400_);
lean_dec(v_key_2399_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_b_2397_);
lean_ctor_set(v___x_2403_, 0, v_a_2396_);
v___x_2411_ = v___x_2403_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2396_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_b_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_tail_2401_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2414_, lean_object* v_x_2415_){
_start:
{
if (lean_obj_tag(v_x_2415_) == 0)
{
return v_x_2414_;
}
else
{
lean_object* v_key_2416_; lean_object* v_value_2417_; lean_object* v_tail_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2441_; 
v_key_2416_ = lean_ctor_get(v_x_2415_, 0);
v_value_2417_ = lean_ctor_get(v_x_2415_, 1);
v_tail_2418_ = lean_ctor_get(v_x_2415_, 2);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_x_2415_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2420_ = v_x_2415_;
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_tail_2418_);
lean_inc(v_value_2417_);
lean_inc(v_key_2416_);
lean_dec(v_x_2415_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2441_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; uint64_t v___x_2423_; uint64_t v___x_2424_; uint64_t v___x_2425_; uint64_t v_fold_2426_; uint64_t v___x_2427_; uint64_t v___x_2428_; uint64_t v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2422_ = lean_array_get_size(v_x_2414_);
v___x_2423_ = l_Lean_ExprStructEq_hash(v_key_2416_);
v___x_2424_ = 32ULL;
v___x_2425_ = lean_uint64_shift_right(v___x_2423_, v___x_2424_);
v_fold_2426_ = lean_uint64_xor(v___x_2423_, v___x_2425_);
v___x_2427_ = 16ULL;
v___x_2428_ = lean_uint64_shift_right(v_fold_2426_, v___x_2427_);
v___x_2429_ = lean_uint64_xor(v_fold_2426_, v___x_2428_);
v___x_2430_ = lean_uint64_to_usize(v___x_2429_);
v___x_2431_ = lean_usize_of_nat(v___x_2422_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_sub(v___x_2431_, v___x_2432_);
v___x_2434_ = lean_usize_land(v___x_2430_, v___x_2433_);
v___x_2435_ = lean_array_uget_borrowed(v_x_2414_, v___x_2434_);
lean_inc(v___x_2435_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 2, v___x_2435_);
v___x_2437_ = v___x_2420_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_key_2416_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_value_2417_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_array_uset(v_x_2414_, v___x_2434_, v___x_2437_);
v_x_2414_ = v___x_2438_;
v_x_2415_ = v_tail_2418_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2442_, lean_object* v_source_2443_, lean_object* v_target_2444_){
_start:
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = lean_array_get_size(v_source_2443_);
v___x_2446_ = lean_nat_dec_lt(v_i_2442_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v_source_2443_);
lean_dec(v_i_2442_);
return v_target_2444_;
}
else
{
lean_object* v_es_2447_; lean_object* v___x_2448_; lean_object* v_source_2449_; lean_object* v_target_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_es_2447_ = lean_array_fget(v_source_2443_, v_i_2442_);
v___x_2448_ = lean_box(0);
v_source_2449_ = lean_array_fset(v_source_2443_, v_i_2442_, v___x_2448_);
v_target_2450_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2444_, v_es_2447_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_add(v_i_2442_, v___x_2451_);
lean_dec(v_i_2442_);
v_i_2442_ = v___x_2452_;
v_source_2443_ = v_source_2449_;
v_target_2444_ = v_target_2450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_nbuckets_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2455_ = lean_array_get_size(v_data_2454_);
v___x_2456_ = lean_unsigned_to_nat(2u);
v_nbuckets_2457_ = lean_nat_mul(v___x_2455_, v___x_2456_);
v___x_2458_ = lean_unsigned_to_nat(0u);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_mk_array(v_nbuckets_2457_, v___x_2459_);
v___x_2461_ = lean_array_propagate_mark(v_data_2454_, v___x_2460_);
v___x_2462_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2458_, v_data_2454_, v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = 0;
return v___x_2465_;
}
else
{
lean_object* v_key_2466_; lean_object* v_tail_2467_; uint8_t v___x_2468_; 
v_key_2466_ = lean_ctor_get(v_x_2464_, 0);
v_tail_2467_ = lean_ctor_get(v_x_2464_, 2);
v___x_2468_ = l_Lean_ExprStructEq_beq(v_key_2466_, v_a_2463_);
if (v___x_2468_ == 0)
{
v_x_2464_ = v_tail_2467_;
goto _start;
}
else
{
return v___x_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2470_, lean_object* v_x_2471_){
_start:
{
uint8_t v_res_2472_; lean_object* v_r_2473_; 
v_res_2472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2470_, v_x_2471_);
lean_dec(v_x_2471_);
lean_dec_ref(v_a_2470_);
v_r_2473_ = lean_box(v_res_2472_);
return v_r_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_){
_start:
{
lean_object* v_size_2477_; lean_object* v_buckets_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2521_; 
v_size_2477_ = lean_ctor_get(v_m_2474_, 0);
v_buckets_2478_ = lean_ctor_get(v_m_2474_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_m_2474_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2480_ = v_m_2474_;
v_isShared_2481_ = v_isSharedCheck_2521_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_buckets_2478_);
lean_inc(v_size_2477_);
lean_dec(v_m_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2521_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v___x_2485_; uint64_t v_fold_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; lean_object* v_bkt_2495_; uint8_t v___x_2496_; 
v___x_2482_ = lean_array_get_size(v_buckets_2478_);
v___x_2483_ = l_Lean_ExprStructEq_hash(v_a_2475_);
v___x_2484_ = 32ULL;
v___x_2485_ = lean_uint64_shift_right(v___x_2483_, v___x_2484_);
v_fold_2486_ = lean_uint64_xor(v___x_2483_, v___x_2485_);
v___x_2487_ = 16ULL;
v___x_2488_ = lean_uint64_shift_right(v_fold_2486_, v___x_2487_);
v___x_2489_ = lean_uint64_xor(v_fold_2486_, v___x_2488_);
v___x_2490_ = lean_uint64_to_usize(v___x_2489_);
v___x_2491_ = lean_usize_of_nat(v___x_2482_);
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_sub(v___x_2491_, v___x_2492_);
v___x_2494_ = lean_usize_land(v___x_2490_, v___x_2493_);
v_bkt_2495_ = lean_array_uget_borrowed(v_buckets_2478_, v___x_2494_);
v___x_2496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2475_, v_bkt_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v_size_x27_2498_; lean_object* v___x_2499_; lean_object* v_buckets_x27_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v_size_x27_2498_ = lean_nat_add(v_size_2477_, v___x_2497_);
lean_dec(v_size_2477_);
lean_inc(v_bkt_2495_);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2475_);
lean_ctor_set(v___x_2499_, 1, v_b_2476_);
lean_ctor_set(v___x_2499_, 2, v_bkt_2495_);
v_buckets_x27_2500_ = lean_array_uset(v_buckets_2478_, v___x_2494_, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(4u);
v___x_2502_ = lean_nat_mul(v_size_x27_2498_, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(3u);
v___x_2504_ = lean_nat_div(v___x_2502_, v___x_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_array_get_size(v_buckets_x27_2500_);
v___x_2506_ = lean_nat_dec_le(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
if (v___x_2506_ == 0)
{
lean_object* v_val_2507_; lean_object* v___x_2509_; 
v_val_2507_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2500_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_val_2507_);
lean_ctor_set(v___x_2480_, 0, v_size_x27_2498_);
v___x_2509_ = v___x_2480_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_size_x27_2498_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_val_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
else
{
lean_object* v___x_2512_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_buckets_x27_2500_);
lean_ctor_set(v___x_2480_, 0, v_size_x27_2498_);
v___x_2512_ = v___x_2480_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_size_x27_2498_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_buckets_x27_2500_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v_buckets_x27_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_inc(v_bkt_2495_);
v___x_2514_ = lean_box(0);
v_buckets_x27_2515_ = lean_array_uset(v_buckets_2478_, v___x_2494_, v___x_2514_);
v___x_2516_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2475_, v_b_2476_, v_bkt_2495_);
v___x_2517_ = lean_array_uset(v_buckets_x27_2515_, v___x_2494_, v___x_2516_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2517_);
v___x_2519_ = v___x_2480_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_2477_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2522_, lean_object* v_e_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_st_ref_take(v_a_2522_);
v___x_2527_ = lean_box(0);
v___x_2528_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2526_, v_e_2523_, v_a_2524_);
v___x_2529_ = lean_st_ref_put(v_a_2522_, v___x_2528_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2530_, lean_object* v_e_2531_, lean_object* v_a_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2530_, v_e_2531_, v_a_2532_);
lean_dec(v_a_2530_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2535_, lean_object* v_x_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_apply_1(v_x_2536_, lean_box(0));
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2544_, v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2552_, lean_object* v_x_2553_){
_start:
{
if (lean_obj_tag(v_x_2553_) == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_box(0);
return v___x_2554_;
}
else
{
lean_object* v_key_2555_; lean_object* v_value_2556_; lean_object* v_tail_2557_; uint8_t v___x_2558_; 
v_key_2555_ = lean_ctor_get(v_x_2553_, 0);
v_value_2556_ = lean_ctor_get(v_x_2553_, 1);
v_tail_2557_ = lean_ctor_get(v_x_2553_, 2);
v___x_2558_ = l_Lean_ExprStructEq_beq(v_key_2555_, v_a_2552_);
if (v___x_2558_ == 0)
{
v_x_2553_ = v_tail_2557_;
goto _start;
}
else
{
lean_object* v___x_2560_; 
lean_inc(v_value_2556_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_value_2556_);
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2561_, lean_object* v_x_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2561_, v_x_2562_);
lean_dec(v_x_2562_);
lean_dec_ref(v_a_2561_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_buckets_2566_; lean_object* v___x_2567_; uint64_t v___x_2568_; uint64_t v___x_2569_; uint64_t v___x_2570_; uint64_t v_fold_2571_; uint64_t v___x_2572_; uint64_t v___x_2573_; uint64_t v___x_2574_; size_t v___x_2575_; size_t v___x_2576_; size_t v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_buckets_2566_ = lean_ctor_get(v_m_2564_, 1);
v___x_2567_ = lean_array_get_size(v_buckets_2566_);
v___x_2568_ = l_Lean_ExprStructEq_hash(v_a_2565_);
v___x_2569_ = 32ULL;
v___x_2570_ = lean_uint64_shift_right(v___x_2568_, v___x_2569_);
v_fold_2571_ = lean_uint64_xor(v___x_2568_, v___x_2570_);
v___x_2572_ = 16ULL;
v___x_2573_ = lean_uint64_shift_right(v_fold_2571_, v___x_2572_);
v___x_2574_ = lean_uint64_xor(v_fold_2571_, v___x_2573_);
v___x_2575_ = lean_uint64_to_usize(v___x_2574_);
v___x_2576_ = lean_usize_of_nat(v___x_2567_);
v___x_2577_ = ((size_t)1ULL);
v___x_2578_ = lean_usize_sub(v___x_2576_, v___x_2577_);
v___x_2579_ = lean_usize_land(v___x_2575_, v___x_2578_);
v___x_2580_ = lean_array_uget_borrowed(v_buckets_2566_, v___x_2579_);
v___x_2581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2565_, v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2582_, v_a_2583_);
lean_dec_ref(v_a_2583_);
lean_dec_ref(v_m_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2585_, lean_object* v___y_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2586_);
v___x_2593_ = lean_apply_7(v_k_2585_, v_b_2587_, v___y_2586_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2594_, lean_object* v___y_2595_, lean_object* v_b_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2594_, v___y_2595_, v_b_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2595_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2603_, uint8_t v_bi_2604_, lean_object* v_type_2605_, lean_object* v_k_2606_, uint8_t v_kind_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___f_2614_; lean_object* v___x_2615_; 
lean_inc(v___y_2608_);
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2614_, 0, v_k_2606_);
lean_closure_set(v___f_2614_, 1, v___y_2608_);
v___x_2615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2603_, v_bi_2604_, v_type_2605_, v___f_2614_, v_kind_2607_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2615_) == 0)
{
return v___x_2615_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2624_, lean_object* v_bi_2625_, lean_object* v_type_2626_, lean_object* v_k_2627_, lean_object* v_kind_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v_bi_boxed_2635_; uint8_t v_kind_boxed_2636_; lean_object* v_res_2637_; 
v_bi_boxed_2635_ = lean_unbox(v_bi_2625_);
v_kind_boxed_2636_ = lean_unbox(v_kind_2628_);
v_res_2637_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2624_, v_bi_boxed_2635_, v_type_2626_, v_k_2627_, v_kind_boxed_2636_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2638_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2652_, lean_object* v_type_2653_, lean_object* v_val_2654_, lean_object* v_k_2655_, uint8_t v_nondep_2656_, uint8_t v_kind_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___f_2664_; lean_object* v___x_2665_; 
lean_inc(v___y_2658_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2664_, 0, v_k_2655_);
lean_closure_set(v___f_2664_, 1, v___y_2658_);
v___x_2665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2652_, v_type_2653_, v_val_2654_, v___f_2664_, v_nondep_2656_, v_kind_2657_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2665_) == 0)
{
return v___x_2665_;
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2674_, lean_object* v_type_2675_, lean_object* v_val_2676_, lean_object* v_k_2677_, lean_object* v_nondep_2678_, lean_object* v_kind_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v_nondep_boxed_2686_; uint8_t v_kind_boxed_2687_; lean_object* v_res_2688_; 
v_nondep_boxed_2686_ = lean_unbox(v_nondep_2678_);
v_kind_boxed_2687_ = lean_unbox(v_kind_2679_);
v_res_2688_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2674_, v_type_2675_, v_val_2676_, v_k_2677_, v_nondep_boxed_2686_, v_kind_boxed_2687_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
return v_res_2688_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = l_Lean_maxRecDepthErrorMessage;
v___x_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2697_ = l_Lean_MessageData_ofFormat(v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2699_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2700_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___x_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_ref_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___y_2717_; lean_object* v_toCold_2726_; lean_object* v_currRecDepth_2727_; lean_object* v_ref_2728_; uint16_t v_optionFlags_2729_; uint8_t v_suppressElabErrors_2730_; uint8_t v_isRecordingDeps_2731_; lean_object* v_maxRecDepth_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_toCold_2726_ = lean_ctor_get(v___y_2713_, 0);
v_currRecDepth_2727_ = lean_ctor_get(v___y_2713_, 1);
v_ref_2728_ = lean_ctor_get(v___y_2713_, 2);
v_optionFlags_2729_ = lean_ctor_get_uint16(v___y_2713_, sizeof(void*)*3);
v_suppressElabErrors_2730_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2731_ = lean_ctor_get_uint8(v___y_2713_, sizeof(void*)*3 + 3);
v_maxRecDepth_2737_ = lean_ctor_get(v_toCold_2726_, 3);
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_nat_dec_eq(v_maxRecDepth_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_nat_dec_eq(v_currRecDepth_2727_, v_maxRecDepth_2737_);
if (v___x_2740_ == 0)
{
goto v___jp_2732_;
}
else
{
lean_object* v___x_2741_; 
lean_dec_ref(v_x_2709_);
lean_inc(v_ref_2728_);
v___x_2741_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2728_);
v___y_2717_ = v___x_2741_;
goto v___jp_2716_;
}
}
else
{
goto v___jp_2732_;
}
v___jp_2716_:
{
if (lean_obj_tag(v___y_2717_) == 0)
{
return v___y_2717_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_a_2718_ = lean_ctor_get(v___y_2717_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___y_2717_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___y_2717_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___y_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2733_ = lean_unsigned_to_nat(1u);
v___x_2734_ = lean_nat_add(v_currRecDepth_2727_, v___x_2733_);
lean_inc(v_ref_2728_);
lean_inc_ref(v_toCold_2726_);
v___x_2735_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2735_, 0, v_toCold_2726_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
lean_ctor_set(v___x_2735_, 2, v_ref_2728_);
lean_ctor_set_uint16(v___x_2735_, sizeof(void*)*3, v_optionFlags_2729_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3 + 2, v_suppressElabErrors_2730_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3 + 3, v_isRecordingDeps_2731_);
lean_inc(v___y_2714_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___y_2710_);
v___x_2736_ = lean_apply_6(v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___x_2735_, v___y_2714_, lean_box(0));
v___y_2717_ = v___x_2736_;
goto v___jp_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2750_, lean_object* v_pre_2751_, lean_object* v_post_2752_, lean_object* v_usedLetOnly_2753_, lean_object* v_skipConstInApp_2754_, lean_object* v_skipInstances_2755_, lean_object* v_body_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v_usedLetOnly_boxed_2764_; uint8_t v_skipConstInApp_boxed_2765_; uint8_t v_skipInstances_boxed_2766_; lean_object* v_res_2767_; 
v_usedLetOnly_boxed_2764_ = lean_unbox(v_usedLetOnly_2753_);
v_skipConstInApp_boxed_2765_ = lean_unbox(v_skipConstInApp_2754_);
v_skipInstances_boxed_2766_ = lean_unbox(v_skipInstances_2755_);
v_res_2767_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2750_, v_pre_2751_, v_post_2752_, v_usedLetOnly_boxed_2764_, v_skipConstInApp_boxed_2765_, v_skipInstances_boxed_2766_, v_body_2756_, v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2771_, lean_object* v_pre_2772_, lean_object* v_post_2773_, uint8_t v_usedLetOnly_2774_, uint8_t v_skipConstInApp_2775_, uint8_t v_skipInstances_2776_, lean_object* v_body_2777_, lean_object* v_x_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_array_push(v_fvars_2771_, v_x_2778_);
v___x_2786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2772_, v_post_2773_, v_usedLetOnly_2774_, v_skipConstInApp_2775_, v_skipInstances_2776_, v___x_2785_, v_body_2777_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2787_, lean_object* v_pre_2788_, lean_object* v_post_2789_, lean_object* v_usedLetOnly_2790_, lean_object* v_skipConstInApp_2791_, lean_object* v_skipInstances_2792_, lean_object* v_body_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
uint8_t v_usedLetOnly_boxed_2801_; uint8_t v_skipConstInApp_boxed_2802_; uint8_t v_skipInstances_boxed_2803_; lean_object* v_res_2804_; 
v_usedLetOnly_boxed_2801_ = lean_unbox(v_usedLetOnly_2790_);
v_skipConstInApp_boxed_2802_ = lean_unbox(v_skipConstInApp_2791_);
v_skipInstances_boxed_2803_ = lean_unbox(v_skipInstances_2792_);
v_res_2804_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2787_, v_pre_2788_, v_post_2789_, v_usedLetOnly_boxed_2801_, v_skipConstInApp_boxed_2802_, v_skipInstances_boxed_2803_, v_body_2793_, v_x_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2805_, lean_object* v_post_2806_, uint8_t v_usedLetOnly_2807_, uint8_t v_skipConstInApp_2808_, uint8_t v_skipInstances_2809_, lean_object* v_e_2810_, lean_object* v_a_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
lean_inc_ref(v_post_2806_);
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc(v___y_2813_);
lean_inc_ref(v___y_2812_);
lean_inc_ref(v_e_2810_);
v___x_2817_ = lean_apply_6(v_post_2806_, v_e_2810_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, lean_box(0));
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2836_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2836_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2836_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
switch(lean_obj_tag(v_a_2818_))
{
case 0:
{
lean_object* v_e_2822_; lean_object* v___x_2824_; 
lean_dec_ref(v_e_2810_);
lean_dec_ref(v_post_2806_);
lean_dec_ref(v_pre_2805_);
v_e_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc_ref(v_e_2822_);
lean_dec_ref_known(v_a_2818_, 1);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_e_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_e_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
case 1:
{
lean_object* v_e_2826_; lean_object* v___x_2827_; 
lean_del_object(v___x_2820_);
lean_dec_ref(v_e_2810_);
v_e_2826_ = lean_ctor_get(v_a_2818_, 0);
lean_inc_ref(v_e_2826_);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2827_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2805_, v_post_2806_, v_usedLetOnly_2807_, v_skipConstInApp_2808_, v_skipInstances_2809_, v_e_2826_, v_a_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2827_;
}
default: 
{
lean_object* v_e_x3f_2828_; 
lean_dec_ref(v_post_2806_);
lean_dec_ref(v_pre_2805_);
v_e_x3f_2828_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_e_x3f_2828_);
lean_dec_ref_known(v_a_2818_, 1);
if (lean_obj_tag(v_e_x3f_2828_) == 0)
{
lean_object* v___x_2830_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_e_2810_);
v___x_2830_ = v___x_2820_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_e_2810_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; 
lean_dec_ref(v_e_2810_);
v_val_2832_ = lean_ctor_get(v_e_x3f_2828_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_e_x3f_2828_, 1);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_val_2832_);
v___x_2834_ = v___x_2820_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_val_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_e_2810_);
lean_dec_ref(v_post_2806_);
lean_dec_ref(v_pre_2805_);
v_a_2837_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2817_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2817_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2845_, lean_object* v_post_2846_, uint8_t v_usedLetOnly_2847_, uint8_t v_skipConstInApp_2848_, uint8_t v_skipInstances_2849_, lean_object* v_fvars_2850_, lean_object* v_e_2851_, lean_object* v_a_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
if (lean_obj_tag(v_e_2851_) == 6)
{
lean_object* v_binderName_2858_; lean_object* v_binderType_2859_; lean_object* v_body_2860_; uint8_t v_binderInfo_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_binderName_2858_ = lean_ctor_get(v_e_2851_, 0);
lean_inc(v_binderName_2858_);
v_binderType_2859_ = lean_ctor_get(v_e_2851_, 1);
lean_inc_ref(v_binderType_2859_);
v_body_2860_ = lean_ctor_get(v_e_2851_, 2);
lean_inc_ref(v_body_2860_);
v_binderInfo_2861_ = lean_ctor_get_uint8(v_e_2851_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2851_, 3);
v___x_2862_ = lean_box(v_usedLetOnly_2847_);
v___x_2863_ = lean_box(v_skipConstInApp_2848_);
v___x_2864_ = lean_box(v_skipInstances_2849_);
lean_inc_ref(v_post_2846_);
lean_inc_ref(v_pre_2845_);
lean_inc_ref(v_fvars_2850_);
v___f_2865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2865_, 0, v_fvars_2850_);
lean_closure_set(v___f_2865_, 1, v_pre_2845_);
lean_closure_set(v___f_2865_, 2, v_post_2846_);
lean_closure_set(v___f_2865_, 3, v___x_2862_);
lean_closure_set(v___f_2865_, 4, v___x_2863_);
lean_closure_set(v___f_2865_, 5, v___x_2864_);
lean_closure_set(v___f_2865_, 6, v_body_2860_);
v___x_2866_ = lean_expr_instantiate_rev(v_binderType_2859_, v_fvars_2850_);
lean_dec_ref(v_fvars_2850_);
lean_dec_ref(v_binderType_2859_);
v___x_2867_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2845_, v_post_2846_, v_usedLetOnly_2847_, v_skipConstInApp_2848_, v_skipInstances_2849_, v___x_2866_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = 0;
v___x_2870_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2858_, v_binderInfo_2861_, v_a_2868_, v___f_2865_, v___x_2869_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2870_;
}
else
{
lean_dec_ref(v___f_2865_);
lean_dec(v_binderName_2858_);
return v___x_2867_;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_expr_instantiate_rev(v_e_2851_, v_fvars_2850_);
lean_dec_ref(v_e_2851_);
lean_inc_ref(v_post_2846_);
lean_inc_ref(v_pre_2845_);
v___x_2872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2845_, v_post_2846_, v_usedLetOnly_2847_, v_skipConstInApp_2848_, v_skipInstances_2849_, v___x_2871_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; uint8_t v___x_2874_; uint8_t v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = 0;
v___x_2875_ = 1;
v___x_2876_ = 1;
v___x_2877_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2850_, v_a_2873_, v___x_2874_, v_usedLetOnly_2847_, v___x_2874_, v___x_2875_, v___x_2876_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec_ref(v_fvars_2850_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2845_, v_post_2846_, v_usedLetOnly_2847_, v_skipConstInApp_2848_, v_skipInstances_2849_, v_a_2878_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2879_;
}
else
{
lean_dec_ref(v_post_2846_);
lean_dec_ref(v_pre_2845_);
return v___x_2877_;
}
}
else
{
lean_dec_ref(v_fvars_2850_);
lean_dec_ref(v_post_2846_);
lean_dec_ref(v_pre_2845_);
return v___x_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2880_, lean_object* v_pre_2881_, lean_object* v_post_2882_, uint8_t v_usedLetOnly_2883_, uint8_t v_skipConstInApp_2884_, uint8_t v_skipInstances_2885_, lean_object* v_body_2886_, lean_object* v_x_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_array_push(v_fvars_2880_, v_x_2887_);
v___x_2895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2881_, v_post_2882_, v_usedLetOnly_2883_, v_skipConstInApp_2884_, v_skipInstances_2885_, v___x_2894_, v_body_2886_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2896_, lean_object* v_pre_2897_, lean_object* v_post_2898_, lean_object* v_usedLetOnly_2899_, lean_object* v_skipConstInApp_2900_, lean_object* v_skipInstances_2901_, lean_object* v_body_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
uint8_t v_usedLetOnly_boxed_2910_; uint8_t v_skipConstInApp_boxed_2911_; uint8_t v_skipInstances_boxed_2912_; lean_object* v_res_2913_; 
v_usedLetOnly_boxed_2910_ = lean_unbox(v_usedLetOnly_2899_);
v_skipConstInApp_boxed_2911_ = lean_unbox(v_skipConstInApp_2900_);
v_skipInstances_boxed_2912_ = lean_unbox(v_skipInstances_2901_);
v_res_2913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2896_, v_pre_2897_, v_post_2898_, v_usedLetOnly_boxed_2910_, v_skipConstInApp_boxed_2911_, v_skipInstances_boxed_2912_, v_body_2902_, v_x_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2914_, lean_object* v_post_2915_, uint8_t v_usedLetOnly_2916_, uint8_t v_skipConstInApp_2917_, uint8_t v_skipInstances_2918_, lean_object* v_fvars_2919_, lean_object* v_e_2920_, lean_object* v_a_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
if (lean_obj_tag(v_e_2920_) == 8)
{
lean_object* v_declName_2927_; lean_object* v_type_2928_; lean_object* v_value_2929_; lean_object* v_body_2930_; uint8_t v_nondep_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_declName_2927_ = lean_ctor_get(v_e_2920_, 0);
lean_inc(v_declName_2927_);
v_type_2928_ = lean_ctor_get(v_e_2920_, 1);
lean_inc_ref(v_type_2928_);
v_value_2929_ = lean_ctor_get(v_e_2920_, 2);
lean_inc_ref(v_value_2929_);
v_body_2930_ = lean_ctor_get(v_e_2920_, 3);
lean_inc_ref(v_body_2930_);
v_nondep_2931_ = lean_ctor_get_uint8(v_e_2920_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2920_, 4);
v___x_2932_ = lean_box(v_usedLetOnly_2916_);
v___x_2933_ = lean_box(v_skipConstInApp_2917_);
v___x_2934_ = lean_box(v_skipInstances_2918_);
lean_inc_ref_n(v_post_2915_, 2);
lean_inc_ref_n(v_pre_2914_, 2);
lean_inc_ref(v_fvars_2919_);
v___f_2935_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2935_, 0, v_fvars_2919_);
lean_closure_set(v___f_2935_, 1, v_pre_2914_);
lean_closure_set(v___f_2935_, 2, v_post_2915_);
lean_closure_set(v___f_2935_, 3, v___x_2932_);
lean_closure_set(v___f_2935_, 4, v___x_2933_);
lean_closure_set(v___f_2935_, 5, v___x_2934_);
lean_closure_set(v___f_2935_, 6, v_body_2930_);
v___x_2936_ = lean_expr_instantiate_rev(v_type_2928_, v_fvars_2919_);
lean_dec_ref(v_type_2928_);
v___x_2937_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2914_, v_post_2915_, v_usedLetOnly_2916_, v_skipConstInApp_2917_, v_skipInstances_2918_, v___x_2936_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = lean_expr_instantiate_rev(v_value_2929_, v_fvars_2919_);
lean_dec_ref(v_fvars_2919_);
lean_dec_ref(v_value_2929_);
v___x_2940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2914_, v_post_2915_, v_usedLetOnly_2916_, v_skipConstInApp_2917_, v_skipInstances_2918_, v___x_2939_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = 0;
v___x_2943_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2927_, v_a_2938_, v_a_2941_, v___f_2935_, v_nondep_2931_, v___x_2942_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2943_;
}
else
{
lean_dec(v_a_2938_);
lean_dec_ref(v___f_2935_);
lean_dec(v_declName_2927_);
return v___x_2940_;
}
}
else
{
lean_dec_ref(v___f_2935_);
lean_dec_ref(v_value_2929_);
lean_dec(v_declName_2927_);
lean_dec_ref(v_fvars_2919_);
lean_dec_ref(v_post_2915_);
lean_dec_ref(v_pre_2914_);
return v___x_2937_;
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_expr_instantiate_rev(v_e_2920_, v_fvars_2919_);
lean_dec_ref(v_e_2920_);
lean_inc_ref(v_post_2915_);
lean_inc_ref(v_pre_2914_);
v___x_2945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2914_, v_post_2915_, v_usedLetOnly_2916_, v_skipConstInApp_2917_, v_skipInstances_2918_, v___x_2944_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; uint8_t v___x_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = 0;
v___x_2948_ = 1;
v___x_2949_ = l_Lean_Meta_mkLetFVars(v_fvars_2919_, v_a_2946_, v_usedLetOnly_2916_, v___x_2947_, v___x_2948_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec_ref(v_fvars_2919_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2914_, v_post_2915_, v_usedLetOnly_2916_, v_skipConstInApp_2917_, v_skipInstances_2918_, v_a_2950_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2951_;
}
else
{
lean_dec_ref(v_post_2915_);
lean_dec_ref(v_pre_2914_);
return v___x_2949_;
}
}
else
{
lean_dec_ref(v_fvars_2919_);
lean_dec_ref(v_post_2915_);
lean_dec_ref(v_pre_2914_);
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2952_, lean_object* v_post_2953_, uint8_t v_usedLetOnly_2954_, uint8_t v_skipConstInApp_2955_, uint8_t v_skipInstances_2956_, size_t v_sz_2957_, size_t v_i_2958_, lean_object* v_bs_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v___x_2966_; 
v___x_2966_ = lean_usize_dec_lt(v_i_2958_, v_sz_2957_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_dec_ref(v_post_2953_);
lean_dec_ref(v_pre_2952_);
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_bs_2959_);
return v___x_2967_;
}
else
{
lean_object* v_v_2968_; lean_object* v___x_2969_; lean_object* v_bs_x27_2970_; lean_object* v___x_2971_; 
v_v_2968_ = lean_array_uget(v_bs_2959_, v_i_2958_);
v___x_2969_ = lean_unsigned_to_nat(0u);
v_bs_x27_2970_ = lean_array_uset(v_bs_2959_, v_i_2958_, v___x_2969_);
lean_inc_ref(v_post_2953_);
lean_inc_ref(v_pre_2952_);
v___x_2971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2952_, v_post_2953_, v_usedLetOnly_2954_, v_skipConstInApp_2955_, v_skipInstances_2956_, v_v_2968_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2958_, v___x_2973_);
v___x_2975_ = lean_array_uset(v_bs_x27_2970_, v_i_2958_, v_a_2972_);
v_i_2958_ = v___x_2974_;
v_bs_2959_ = v___x_2975_;
goto _start;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v_bs_x27_2970_);
lean_dec_ref(v_post_2953_);
lean_dec_ref(v_pre_2952_);
v_a_2977_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2971_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2971_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2985_, lean_object* v_post_2986_, uint8_t v_usedLetOnly_2987_, uint8_t v_skipConstInApp_2988_, uint8_t v_skipInstances_2989_, lean_object* v___x_2990_, lean_object* v___y_2991_, lean_object* v_b_2992_, lean_object* v_a_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2985_, v_post_2986_, v_usedLetOnly_2987_, v_skipConstInApp_2988_, v_skipInstances_2989_, v___x_2990_, v___y_2991_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3009_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3002_ = v___x_2999_;
v_isShared_3003_ = v_isSharedCheck_3009_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2999_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3009_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3004_ = lean_array_fset(v_b_2992_, v_a_2993_, v_a_3000_);
v___x_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3005_);
v___x_3007_ = v___x_3002_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_b_2992_);
v_a_3010_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2999_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2999_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3018_, lean_object* v_post_3019_, lean_object* v_usedLetOnly_3020_, lean_object* v_skipConstInApp_3021_, lean_object* v_skipInstances_3022_, lean_object* v___x_3023_, lean_object* v___y_3024_, lean_object* v_b_3025_, lean_object* v_a_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
uint8_t v_usedLetOnly_boxed_3032_; uint8_t v_skipConstInApp_boxed_3033_; uint8_t v_skipInstances_boxed_3034_; lean_object* v_res_3035_; 
v_usedLetOnly_boxed_3032_ = lean_unbox(v_usedLetOnly_3020_);
v_skipConstInApp_boxed_3033_ = lean_unbox(v_skipConstInApp_3021_);
v_skipInstances_boxed_3034_ = lean_unbox(v_skipInstances_3022_);
v_res_3035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3018_, v_post_3019_, v_usedLetOnly_boxed_3032_, v_skipConstInApp_boxed_3033_, v_skipInstances_boxed_3034_, v___x_3023_, v___y_3024_, v_b_3025_, v_a_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v_a_3026_);
lean_dec(v___y_3024_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3036_, lean_object* v___x_3037_, lean_object* v_pre_3038_, lean_object* v_post_3039_, uint8_t v_usedLetOnly_3040_, uint8_t v_skipConstInApp_3041_, uint8_t v_skipInstances_3042_, lean_object* v_a_3043_, lean_object* v_b_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v___y_3052_; uint8_t v___x_3075_; 
v___x_3075_ = lean_nat_dec_lt(v_a_3043_, v_upperBound_3036_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_post_3039_);
lean_dec_ref(v_pre_3038_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3044_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_array_fget_borrowed(v_b_3044_, v_a_3043_);
v___x_3078_ = lean_array_get_size(v___x_3037_);
v___x_3079_ = lean_nat_dec_lt(v_a_3043_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; 
lean_inc(v___x_3077_);
v___x_3080_ = lean_box(v_usedLetOnly_3040_);
v___x_3081_ = lean_box(v_skipConstInApp_3041_);
v___x_3082_ = lean_box(v_skipInstances_3042_);
lean_inc(v_a_3043_);
lean_inc(v___y_3045_);
lean_inc_ref(v_post_3039_);
lean_inc_ref(v_pre_3038_);
v___f_3083_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3083_, 0, v_pre_3038_);
lean_closure_set(v___f_3083_, 1, v_post_3039_);
lean_closure_set(v___f_3083_, 2, v___x_3080_);
lean_closure_set(v___f_3083_, 3, v___x_3081_);
lean_closure_set(v___f_3083_, 4, v___x_3082_);
lean_closure_set(v___f_3083_, 5, v___x_3077_);
lean_closure_set(v___f_3083_, 6, v___y_3045_);
lean_closure_set(v___f_3083_, 7, v_b_3044_);
lean_closure_set(v___f_3083_, 8, v_a_3043_);
v___y_3052_ = v___f_3083_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3084_; uint8_t v_isInstance_3085_; 
v___x_3084_ = lean_array_fget_borrowed(v___x_3037_, v_a_3043_);
v_isInstance_3085_ = lean_ctor_get_uint8(v___x_3084_, sizeof(void*)*1 + 4);
if (v_isInstance_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; 
lean_inc(v___x_3077_);
v___x_3086_ = lean_box(v_usedLetOnly_3040_);
v___x_3087_ = lean_box(v_skipConstInApp_3041_);
v___x_3088_ = lean_box(v_skipInstances_3042_);
lean_inc(v_a_3043_);
lean_inc(v___y_3045_);
lean_inc_ref(v_post_3039_);
lean_inc_ref(v_pre_3038_);
v___f_3089_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3089_, 0, v_pre_3038_);
lean_closure_set(v___f_3089_, 1, v_post_3039_);
lean_closure_set(v___f_3089_, 2, v___x_3086_);
lean_closure_set(v___f_3089_, 3, v___x_3087_);
lean_closure_set(v___f_3089_, 4, v___x_3088_);
lean_closure_set(v___f_3089_, 5, v___x_3077_);
lean_closure_set(v___f_3089_, 6, v___y_3045_);
lean_closure_set(v___f_3089_, 7, v_b_3044_);
lean_closure_set(v___f_3089_, 8, v_a_3043_);
v___y_3052_ = v___f_3089_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3090_; lean_object* v___f_3091_; 
v___x_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3090_, 0, v_b_3044_);
v___f_3091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3091_, 0, v___x_3090_);
v___y_3052_ = v___f_3091_;
goto v___jp_3051_;
}
}
}
v___jp_3051_:
{
lean_object* v___x_3053_; 
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
v___x_3053_ = lean_apply_5(v___y_3052_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, lean_box(0));
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3066_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
if (lean_obj_tag(v_a_3054_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_post_3039_);
lean_dec_ref(v_pre_3038_);
v_a_3058_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v_a_3054_, 1);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v_a_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_del_object(v___x_3056_);
v_a_3062_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v_a_3054_, 1);
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_add(v_a_3043_, v___x_3063_);
lean_dec(v_a_3043_);
v_a_3043_ = v___x_3064_;
v_b_3044_ = v_a_3062_;
goto _start;
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_post_3039_);
lean_dec_ref(v_pre_3038_);
v_a_3067_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3053_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3053_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3092_, lean_object* v_pre_3093_, lean_object* v_post_3094_, uint8_t v_usedLetOnly_3095_, uint8_t v_skipConstInApp_3096_, lean_object* v_x_3097_, lean_object* v_x_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_f_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; 
if (lean_obj_tag(v_x_3097_) == 5)
{
lean_object* v_fn_3155_; lean_object* v_arg_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_fn_3155_ = lean_ctor_get(v_x_3097_, 0);
lean_inc_ref(v_fn_3155_);
v_arg_3156_ = lean_ctor_get(v_x_3097_, 1);
lean_inc_ref(v_arg_3156_);
lean_dec_ref_known(v_x_3097_, 2);
v___x_3157_ = lean_array_set(v_x_3098_, v_x_3099_, v_arg_3156_);
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_sub(v_x_3099_, v___x_3158_);
lean_dec(v_x_3099_);
v_x_3097_ = v_fn_3155_;
v_x_3098_ = v___x_3157_;
v_x_3099_ = v___x_3159_;
goto _start;
}
else
{
lean_dec(v_x_3099_);
if (v_skipConstInApp_3096_ == 0)
{
goto v___jp_3152_;
}
else
{
uint8_t v___x_3161_; 
v___x_3161_ = l_Lean_Expr_isConst(v_x_3097_);
if (v___x_3161_ == 0)
{
goto v___jp_3152_;
}
else
{
v_f_3107_ = v_x_3097_;
v___y_3108_ = v___y_3100_;
v___y_3109_ = v___y_3101_;
v___y_3110_ = v___y_3102_;
v___y_3111_ = v___y_3103_;
v___y_3112_ = v___y_3104_;
goto v___jp_3106_;
}
}
}
v___jp_3106_:
{
if (v_skipInstances_3092_ == 0)
{
size_t v_sz_3113_; size_t v___x_3114_; lean_object* v___x_3115_; 
v_sz_3113_ = lean_array_size(v_x_3098_);
v___x_3114_ = ((size_t)0ULL);
lean_inc_ref(v_post_3094_);
lean_inc_ref(v_pre_3093_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3092_, v_sz_3113_, v___x_3114_, v_x_3098_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3117_ = l_Lean_mkAppN(v_f_3107_, v_a_3116_);
lean_dec(v_a_3116_);
v___x_3118_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3092_, v___x_3117_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3118_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_f_3107_);
lean_dec_ref(v_post_3094_);
lean_dec_ref(v_pre_3093_);
v_a_3119_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3115_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3115_);
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
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_array_get_size(v_x_3098_);
lean_inc_ref(v_f_3107_);
v___x_3128_ = l_Lean_Meta_getFunInfoNArgs(v_f_3107_, v___x_3127_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v_paramInfo_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v_paramInfo_3130_ = lean_ctor_get(v_a_3129_, 0);
lean_inc_ref(v_paramInfo_3130_);
lean_dec(v_a_3129_);
v___x_3131_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3094_);
lean_inc_ref(v_pre_3093_);
v___x_3132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3127_, v_paramInfo_3130_, v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3092_, v___x_3131_, v_x_3098_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec_ref(v_paramInfo_3130_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = l_Lean_mkAppN(v_f_3107_, v_a_3133_);
lean_dec(v_a_3133_);
v___x_3135_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3092_, v___x_3134_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3135_;
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_f_3107_);
lean_dec_ref(v_post_3094_);
lean_dec_ref(v_pre_3093_);
v_a_3136_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3132_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3132_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v_f_3107_);
lean_dec_ref(v_x_3098_);
lean_dec_ref(v_post_3094_);
lean_dec_ref(v_pre_3093_);
v_a_3144_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3128_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3128_);
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
}
v___jp_3152_:
{
lean_object* v___x_3153_; 
lean_inc_ref(v_post_3094_);
lean_inc_ref(v_pre_3093_);
v___x_3153_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3093_, v_post_3094_, v_usedLetOnly_3095_, v_skipConstInApp_3096_, v_skipInstances_3092_, v_x_3097_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v_f_3107_ = v_a_3154_;
v___y_3108_ = v___y_3100_;
v___y_3109_ = v___y_3101_;
v___y_3110_ = v___y_3102_;
v___y_3111_ = v___y_3103_;
v___y_3112_ = v___y_3104_;
goto v___jp_3106_;
}
else
{
lean_dec_ref(v_x_3098_);
lean_dec_ref(v_post_3094_);
lean_dec_ref(v_pre_3093_);
return v___x_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3162_, lean_object* v_pre_3163_, lean_object* v_e_3164_, lean_object* v_post_3165_, uint8_t v_usedLetOnly_3166_, uint8_t v_skipConstInApp_3167_, uint8_t v_skipInstances_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Core_checkSystem(v___x_3162_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3175_, 1);
lean_inc_ref(v_pre_3163_);
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc(v___y_3171_);
lean_inc_ref(v___y_3170_);
lean_inc_ref(v_e_3164_);
v___x_3176_ = lean_apply_6(v_pre_3163_, v_e_3164_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, lean_box(0));
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3225_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3225_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3225_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___y_3182_; 
switch(lean_obj_tag(v_a_3177_))
{
case 0:
{
lean_object* v_e_3217_; lean_object* v___x_3219_; 
lean_dec_ref(v_post_3165_);
lean_dec_ref(v_e_3164_);
lean_dec_ref(v_pre_3163_);
v_e_3217_ = lean_ctor_get(v_a_3177_, 0);
lean_inc_ref(v_e_3217_);
lean_dec_ref_known(v_a_3177_, 1);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v_e_3217_);
v___x_3219_ = v___x_3179_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_e_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
case 1:
{
lean_object* v_e_3221_; lean_object* v___x_3222_; 
lean_del_object(v___x_3179_);
lean_dec_ref(v_e_3164_);
v_e_3221_ = lean_ctor_get(v_a_3177_, 0);
lean_inc_ref(v_e_3221_);
lean_dec_ref_known(v_a_3177_, 1);
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v_e_3221_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3222_;
}
default: 
{
lean_object* v_e_x3f_3223_; 
lean_del_object(v___x_3179_);
v_e_x3f_3223_ = lean_ctor_get(v_a_3177_, 0);
lean_inc(v_e_x3f_3223_);
lean_dec_ref_known(v_a_3177_, 1);
if (lean_obj_tag(v_e_x3f_3223_) == 0)
{
v___y_3182_ = v_e_3164_;
goto v___jp_3181_;
}
else
{
lean_object* v_val_3224_; 
lean_dec_ref(v_e_3164_);
v_val_3224_ = lean_ctor_get(v_e_x3f_3223_, 0);
lean_inc(v_val_3224_);
lean_dec_ref_known(v_e_x3f_3223_, 1);
v___y_3182_ = v_val_3224_;
goto v___jp_3181_;
}
}
}
v___jp_3181_:
{
switch(lean_obj_tag(v___y_3182_))
{
case 7:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___x_3183_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3184_;
}
case 6:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___x_3185_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3186_;
}
case 8:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___x_3187_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3188_;
}
case 5:
{
lean_object* v_dummy_3189_; lean_object* v_nargs_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_dummy_3189_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3190_ = l_Lean_Expr_getAppNumArgs(v___y_3182_);
lean_inc(v_nargs_3190_);
v___x_3191_ = lean_mk_array(v_nargs_3190_, v_dummy_3189_);
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_nat_sub(v_nargs_3190_, v___x_3192_);
lean_dec(v_nargs_3190_);
v___x_3194_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3168_, v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v___y_3182_, v___x_3191_, v___x_3193_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3194_;
}
case 10:
{
lean_object* v_data_3195_; lean_object* v_expr_3196_; lean_object* v___x_3197_; 
v_data_3195_ = lean_ctor_get(v___y_3182_, 0);
v_expr_3196_ = lean_ctor_get(v___y_3182_, 1);
lean_inc_ref(v_expr_3196_);
lean_inc_ref(v_post_3165_);
lean_inc_ref(v_pre_3163_);
v___x_3197_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v_expr_3196_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; size_t v___x_3199_; size_t v___x_3200_; uint8_t v___x_3201_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = lean_ptr_addr(v_expr_3196_);
v___x_3200_ = lean_ptr_addr(v_a_3198_);
v___x_3201_ = lean_usize_dec_eq(v___x_3199_, v___x_3200_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_inc(v_data_3195_);
lean_dec_ref_known(v___y_3182_, 2);
v___x_3202_ = l_Lean_Expr_mdata___override(v_data_3195_, v_a_3198_);
v___x_3203_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___x_3202_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; 
lean_dec(v_a_3198_);
v___x_3204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3204_;
}
}
else
{
lean_dec_ref_known(v___y_3182_, 2);
lean_dec_ref(v_post_3165_);
lean_dec_ref(v_pre_3163_);
return v___x_3197_;
}
}
case 11:
{
lean_object* v_typeName_3205_; lean_object* v_idx_3206_; lean_object* v_struct_3207_; lean_object* v___x_3208_; 
v_typeName_3205_ = lean_ctor_get(v___y_3182_, 0);
v_idx_3206_ = lean_ctor_get(v___y_3182_, 1);
v_struct_3207_ = lean_ctor_get(v___y_3182_, 2);
lean_inc_ref(v_struct_3207_);
lean_inc_ref(v_post_3165_);
lean_inc_ref(v_pre_3163_);
v___x_3208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v_struct_3207_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; size_t v___x_3210_; size_t v___x_3211_; uint8_t v___x_3212_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = lean_ptr_addr(v_struct_3207_);
v___x_3211_ = lean_ptr_addr(v_a_3209_);
v___x_3212_ = lean_usize_dec_eq(v___x_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_inc(v_idx_3206_);
lean_inc(v_typeName_3205_);
lean_dec_ref_known(v___y_3182_, 3);
v___x_3213_ = l_Lean_Expr_proj___override(v_typeName_3205_, v_idx_3206_, v_a_3209_);
v___x_3214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___x_3213_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3214_;
}
else
{
lean_object* v___x_3215_; 
lean_dec(v_a_3209_);
v___x_3215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3215_;
}
}
else
{
lean_dec_ref_known(v___y_3182_, 3);
lean_dec_ref(v_post_3165_);
lean_dec_ref(v_pre_3163_);
return v___x_3208_;
}
}
default: 
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3163_, v_post_3165_, v_usedLetOnly_3166_, v_skipConstInApp_3167_, v_skipInstances_3168_, v___y_3182_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3216_;
}
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v_post_3165_);
lean_dec_ref(v_e_3164_);
lean_dec_ref(v_pre_3163_);
v_a_3226_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3176_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3176_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_post_3165_);
lean_dec_ref(v_e_3164_);
lean_dec_ref(v_pre_3163_);
v_a_3234_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3175_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3175_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3242_, lean_object* v_pre_3243_, lean_object* v_e_3244_, lean_object* v_post_3245_, lean_object* v_usedLetOnly_3246_, lean_object* v_skipConstInApp_3247_, lean_object* v_skipInstances_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
uint8_t v_usedLetOnly_boxed_3255_; uint8_t v_skipConstInApp_boxed_3256_; uint8_t v_skipInstances_boxed_3257_; lean_object* v_res_3258_; 
v_usedLetOnly_boxed_3255_ = lean_unbox(v_usedLetOnly_3246_);
v_skipConstInApp_boxed_3256_ = lean_unbox(v_skipConstInApp_3247_);
v_skipInstances_boxed_3257_ = lean_unbox(v_skipInstances_3248_);
v_res_3258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3242_, v_pre_3243_, v_e_3244_, v_post_3245_, v_usedLetOnly_boxed_3255_, v_skipConstInApp_boxed_3256_, v_skipInstances_boxed_3257_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3259_, lean_object* v_post_3260_, uint8_t v_usedLetOnly_3261_, uint8_t v_skipConstInApp_3262_, uint8_t v_skipInstances_3263_, lean_object* v_e_3264_, lean_object* v_a_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_inc(v_a_3265_);
v___x_3271_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3271_, 0, lean_box(0));
lean_closure_set(v___x_3271_, 1, lean_box(0));
lean_closure_set(v___x_3271_, 2, v_a_3265_);
v___x_3272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3271_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3307_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3307_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3307_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3273_, v_e_3264_);
lean_dec(v_a_3273_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; 
lean_del_object(v___x_3275_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3279_ = lean_box(v_usedLetOnly_3261_);
v___x_3280_ = lean_box(v_skipConstInApp_3262_);
v___x_3281_ = lean_box(v_skipInstances_3263_);
lean_inc_ref(v_e_3264_);
v___f_3282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3282_, 0, v___x_3278_);
lean_closure_set(v___f_3282_, 1, v_pre_3259_);
lean_closure_set(v___f_3282_, 2, v_e_3264_);
lean_closure_set(v___f_3282_, 3, v_post_3260_);
lean_closure_set(v___f_3282_, 4, v___x_3279_);
lean_closure_set(v___f_3282_, 5, v___x_3280_);
lean_closure_set(v___f_3282_, 6, v___x_3281_);
v___x_3283_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3282_, v_a_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___f_3285_; lean_object* v___x_3286_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc_n(v_a_3284_, 2);
lean_dec_ref_known(v___x_3283_, 1);
lean_inc(v_a_3265_);
v___f_3285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3285_, 0, v_a_3265_);
lean_closure_set(v___f_3285_, 1, v_e_3264_);
lean_closure_set(v___f_3285_, 2, v_a_3284_);
v___x_3286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3285_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3286_, 0);
lean_dec(v_unused_3294_);
v___x_3288_ = v___x_3286_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_dec(v___x_3286_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_a_3284_);
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3284_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_a_3284_);
v_a_3295_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3286_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3286_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_dec_ref(v_e_3264_);
return v___x_3283_;
}
}
else
{
lean_object* v_val_3303_; lean_object* v___x_3305_; 
lean_dec_ref(v_e_3264_);
lean_dec_ref(v_post_3260_);
lean_dec_ref(v_pre_3259_);
v_val_3303_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_val_3303_);
lean_dec_ref_known(v___x_3277_, 1);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v_val_3303_);
v___x_3305_ = v___x_3275_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v_e_3264_);
lean_dec_ref(v_post_3260_);
lean_dec_ref(v_pre_3259_);
v_a_3308_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3272_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3272_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3316_, lean_object* v_post_3317_, uint8_t v_usedLetOnly_3318_, uint8_t v_skipConstInApp_3319_, uint8_t v_skipInstances_3320_, lean_object* v_fvars_3321_, lean_object* v_e_3322_, lean_object* v_a_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
if (lean_obj_tag(v_e_3322_) == 7)
{
lean_object* v_binderName_3329_; lean_object* v_binderType_3330_; lean_object* v_body_3331_; uint8_t v_binderInfo_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_binderName_3329_ = lean_ctor_get(v_e_3322_, 0);
lean_inc(v_binderName_3329_);
v_binderType_3330_ = lean_ctor_get(v_e_3322_, 1);
lean_inc_ref(v_binderType_3330_);
v_body_3331_ = lean_ctor_get(v_e_3322_, 2);
lean_inc_ref(v_body_3331_);
v_binderInfo_3332_ = lean_ctor_get_uint8(v_e_3322_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3322_, 3);
v___x_3333_ = lean_box(v_usedLetOnly_3318_);
v___x_3334_ = lean_box(v_skipConstInApp_3319_);
v___x_3335_ = lean_box(v_skipInstances_3320_);
lean_inc_ref(v_post_3317_);
lean_inc_ref(v_pre_3316_);
lean_inc_ref(v_fvars_3321_);
v___f_3336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3336_, 0, v_fvars_3321_);
lean_closure_set(v___f_3336_, 1, v_pre_3316_);
lean_closure_set(v___f_3336_, 2, v_post_3317_);
lean_closure_set(v___f_3336_, 3, v___x_3333_);
lean_closure_set(v___f_3336_, 4, v___x_3334_);
lean_closure_set(v___f_3336_, 5, v___x_3335_);
lean_closure_set(v___f_3336_, 6, v_body_3331_);
v___x_3337_ = lean_expr_instantiate_rev(v_binderType_3330_, v_fvars_3321_);
lean_dec_ref(v_fvars_3321_);
lean_dec_ref(v_binderType_3330_);
v___x_3338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3316_, v_post_3317_, v_usedLetOnly_3318_, v_skipConstInApp_3319_, v_skipInstances_3320_, v___x_3337_, v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = 0;
v___x_3341_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3329_, v_binderInfo_3332_, v_a_3339_, v___f_3336_, v___x_3340_, v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3341_;
}
else
{
lean_dec_ref(v___f_3336_);
lean_dec(v_binderName_3329_);
return v___x_3338_;
}
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = lean_expr_instantiate_rev(v_e_3322_, v_fvars_3321_);
lean_dec_ref(v_e_3322_);
lean_inc_ref(v_post_3317_);
lean_inc_ref(v_pre_3316_);
v___x_3343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3316_, v_post_3317_, v_usedLetOnly_3318_, v_skipConstInApp_3319_, v_skipInstances_3320_, v___x_3342_, v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; uint8_t v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = 0;
v___x_3346_ = 1;
v___x_3347_ = 1;
v___x_3348_ = l_Lean_Meta_mkForallFVars(v_fvars_3321_, v_a_3344_, v___x_3345_, v_usedLetOnly_3318_, v___x_3346_, v___x_3347_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec_ref(v_fvars_3321_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___x_3350_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3316_, v_post_3317_, v_usedLetOnly_3318_, v_skipConstInApp_3319_, v_skipInstances_3320_, v_a_3349_, v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3350_;
}
else
{
lean_dec_ref(v_post_3317_);
lean_dec_ref(v_pre_3316_);
return v___x_3348_;
}
}
else
{
lean_dec_ref(v_fvars_3321_);
lean_dec_ref(v_post_3317_);
lean_dec_ref(v_pre_3316_);
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3351_, lean_object* v_pre_3352_, lean_object* v_post_3353_, uint8_t v_usedLetOnly_3354_, uint8_t v_skipConstInApp_3355_, uint8_t v_skipInstances_3356_, lean_object* v_body_3357_, lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_array_push(v_fvars_3351_, v_x_3358_);
v___x_3366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3352_, v_post_3353_, v_usedLetOnly_3354_, v_skipConstInApp_3355_, v_skipInstances_3356_, v___x_3365_, v_body_3357_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3367_, lean_object* v_post_3368_, lean_object* v_usedLetOnly_3369_, lean_object* v_skipConstInApp_3370_, lean_object* v_skipInstances_3371_, lean_object* v_e_3372_, lean_object* v_a_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v_usedLetOnly_boxed_3379_; uint8_t v_skipConstInApp_boxed_3380_; uint8_t v_skipInstances_boxed_3381_; lean_object* v_res_3382_; 
v_usedLetOnly_boxed_3379_ = lean_unbox(v_usedLetOnly_3369_);
v_skipConstInApp_boxed_3380_ = lean_unbox(v_skipConstInApp_3370_);
v_skipInstances_boxed_3381_ = lean_unbox(v_skipInstances_3371_);
v_res_3382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3367_, v_post_3368_, v_usedLetOnly_boxed_3379_, v_skipConstInApp_boxed_3380_, v_skipInstances_boxed_3381_, v_e_3372_, v_a_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v_a_3373_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3383_, lean_object* v_post_3384_, lean_object* v_usedLetOnly_3385_, lean_object* v_skipConstInApp_3386_, lean_object* v_skipInstances_3387_, lean_object* v_sz_3388_, lean_object* v_i_3389_, lean_object* v_bs_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
uint8_t v_usedLetOnly_boxed_3397_; uint8_t v_skipConstInApp_boxed_3398_; uint8_t v_skipInstances_boxed_3399_; size_t v_sz_boxed_3400_; size_t v_i_boxed_3401_; lean_object* v_res_3402_; 
v_usedLetOnly_boxed_3397_ = lean_unbox(v_usedLetOnly_3385_);
v_skipConstInApp_boxed_3398_ = lean_unbox(v_skipConstInApp_3386_);
v_skipInstances_boxed_3399_ = lean_unbox(v_skipInstances_3387_);
v_sz_boxed_3400_ = lean_unbox_usize(v_sz_3388_);
lean_dec(v_sz_3388_);
v_i_boxed_3401_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_res_3402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3383_, v_post_3384_, v_usedLetOnly_boxed_3397_, v_skipConstInApp_boxed_3398_, v_skipInstances_boxed_3399_, v_sz_boxed_3400_, v_i_boxed_3401_, v_bs_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3403_, lean_object* v_post_3404_, lean_object* v_usedLetOnly_3405_, lean_object* v_skipConstInApp_3406_, lean_object* v_skipInstances_3407_, lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v_usedLetOnly_boxed_3415_; uint8_t v_skipConstInApp_boxed_3416_; uint8_t v_skipInstances_boxed_3417_; lean_object* v_res_3418_; 
v_usedLetOnly_boxed_3415_ = lean_unbox(v_usedLetOnly_3405_);
v_skipConstInApp_boxed_3416_ = lean_unbox(v_skipConstInApp_3406_);
v_skipInstances_boxed_3417_ = lean_unbox(v_skipInstances_3407_);
v_res_3418_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3403_, v_post_3404_, v_usedLetOnly_boxed_3415_, v_skipConstInApp_boxed_3416_, v_skipInstances_boxed_3417_, v_e_3408_, v_a_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_a_3409_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3419_, lean_object* v_post_3420_, lean_object* v_usedLetOnly_3421_, lean_object* v_skipConstInApp_3422_, lean_object* v_skipInstances_3423_, lean_object* v_fvars_3424_, lean_object* v_e_3425_, lean_object* v_a_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v_usedLetOnly_boxed_3432_; uint8_t v_skipConstInApp_boxed_3433_; uint8_t v_skipInstances_boxed_3434_; lean_object* v_res_3435_; 
v_usedLetOnly_boxed_3432_ = lean_unbox(v_usedLetOnly_3421_);
v_skipConstInApp_boxed_3433_ = lean_unbox(v_skipConstInApp_3422_);
v_skipInstances_boxed_3434_ = lean_unbox(v_skipInstances_3423_);
v_res_3435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3419_, v_post_3420_, v_usedLetOnly_boxed_3432_, v_skipConstInApp_boxed_3433_, v_skipInstances_boxed_3434_, v_fvars_3424_, v_e_3425_, v_a_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v_a_3426_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3436_, lean_object* v_post_3437_, lean_object* v_usedLetOnly_3438_, lean_object* v_skipConstInApp_3439_, lean_object* v_skipInstances_3440_, lean_object* v_fvars_3441_, lean_object* v_e_3442_, lean_object* v_a_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
uint8_t v_usedLetOnly_boxed_3449_; uint8_t v_skipConstInApp_boxed_3450_; uint8_t v_skipInstances_boxed_3451_; lean_object* v_res_3452_; 
v_usedLetOnly_boxed_3449_ = lean_unbox(v_usedLetOnly_3438_);
v_skipConstInApp_boxed_3450_ = lean_unbox(v_skipConstInApp_3439_);
v_skipInstances_boxed_3451_ = lean_unbox(v_skipInstances_3440_);
v_res_3452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3436_, v_post_3437_, v_usedLetOnly_boxed_3449_, v_skipConstInApp_boxed_3450_, v_skipInstances_boxed_3451_, v_fvars_3441_, v_e_3442_, v_a_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v_a_3443_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3453_, lean_object* v_post_3454_, lean_object* v_usedLetOnly_3455_, lean_object* v_skipConstInApp_3456_, lean_object* v_skipInstances_3457_, lean_object* v_fvars_3458_, lean_object* v_e_3459_, lean_object* v_a_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v_usedLetOnly_boxed_3466_; uint8_t v_skipConstInApp_boxed_3467_; uint8_t v_skipInstances_boxed_3468_; lean_object* v_res_3469_; 
v_usedLetOnly_boxed_3466_ = lean_unbox(v_usedLetOnly_3455_);
v_skipConstInApp_boxed_3467_ = lean_unbox(v_skipConstInApp_3456_);
v_skipInstances_boxed_3468_ = lean_unbox(v_skipInstances_3457_);
v_res_3469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3453_, v_post_3454_, v_usedLetOnly_boxed_3466_, v_skipConstInApp_boxed_3467_, v_skipInstances_boxed_3468_, v_fvars_3458_, v_e_3459_, v_a_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v_a_3460_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3470_, lean_object* v___x_3471_, lean_object* v_pre_3472_, lean_object* v_post_3473_, lean_object* v_usedLetOnly_3474_, lean_object* v_skipConstInApp_3475_, lean_object* v_skipInstances_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
uint8_t v_usedLetOnly_boxed_3485_; uint8_t v_skipConstInApp_boxed_3486_; uint8_t v_skipInstances_boxed_3487_; lean_object* v_res_3488_; 
v_usedLetOnly_boxed_3485_ = lean_unbox(v_usedLetOnly_3474_);
v_skipConstInApp_boxed_3486_ = lean_unbox(v_skipConstInApp_3475_);
v_skipInstances_boxed_3487_ = lean_unbox(v_skipInstances_3476_);
v_res_3488_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3470_, v___x_3471_, v_pre_3472_, v_post_3473_, v_usedLetOnly_boxed_3485_, v_skipConstInApp_boxed_3486_, v_skipInstances_boxed_3487_, v_a_3477_, v_b_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___x_3471_);
lean_dec(v_upperBound_3470_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3489_, lean_object* v_pre_3490_, lean_object* v_post_3491_, lean_object* v_usedLetOnly_3492_, lean_object* v_skipConstInApp_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
uint8_t v_skipInstances_boxed_3503_; uint8_t v_usedLetOnly_boxed_3504_; uint8_t v_skipConstInApp_boxed_3505_; lean_object* v_res_3506_; 
v_skipInstances_boxed_3503_ = lean_unbox(v_skipInstances_3489_);
v_usedLetOnly_boxed_3504_ = lean_unbox(v_usedLetOnly_3492_);
v_skipConstInApp_boxed_3505_ = lean_unbox(v_skipConstInApp_3493_);
v_res_3506_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3503_, v_pre_3490_, v_post_3491_, v_usedLetOnly_boxed_3504_, v_skipConstInApp_boxed_3505_, v_x_3494_, v_x_3495_, v_x_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
return v_res_3506_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3507_ = lean_box(0);
v___x_3508_ = lean_unsigned_to_nat(16u);
v___x_3509_ = lean_mk_array(v___x_3508_, v___x_3507_);
return v___x_3509_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3510_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3514_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3514_, 0, lean_box(0));
lean_closure_set(v___x_3514_, 1, lean_box(0));
lean_closure_set(v___x_3514_, 2, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3515_, lean_object* v_pre_3516_, lean_object* v_post_3517_, uint8_t v_usedLetOnly_3518_, uint8_t v_skipConstInApp_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v_a_3528_; lean_object* v___x_3529_; 
v___x_3525_ = 0;
v___x_3526_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3527_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3526_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref(v___x_3527_);
v___x_3529_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3516_, v_post_3517_, v_usedLetOnly_3518_, v_skipConstInApp_3519_, v___x_3525_, v_input_3515_, v_a_3528_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___x_3531_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3531_, 0, lean_box(0));
lean_closure_set(v___x_3531_, 1, lean_box(0));
lean_closure_set(v___x_3531_, 2, v_a_3528_);
v___x_3532_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3531_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3532_, 0);
lean_dec(v_unused_3540_);
v___x_3534_ = v___x_3532_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_dec(v___x_3532_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v_a_3530_);
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3530_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_dec(v_a_3528_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3541_, lean_object* v_pre_3542_, lean_object* v_post_3543_, lean_object* v_usedLetOnly_3544_, lean_object* v_skipConstInApp_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v_usedLetOnly_boxed_3551_; uint8_t v_skipConstInApp_boxed_3552_; lean_object* v_res_3553_; 
v_usedLetOnly_boxed_3551_ = lean_unbox(v_usedLetOnly_3544_);
v_skipConstInApp_boxed_3552_ = lean_unbox(v_skipConstInApp_3545_);
v_res_3553_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3541_, v_pre_3542_, v_post_3543_, v_usedLetOnly_boxed_3551_, v_skipConstInApp_boxed_3552_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3555_, lean_object* v_p_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; lean_object* v_a_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; 
v___f_3562_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3563_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3563_, 0, v_p_3556_);
v___x_3564_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3555_, v_a_3558_);
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = 0;
v___x_3567_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3565_, v___f_3562_, v___f_3563_, v___x_3566_, v___x_3566_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3568_, lean_object* v_p_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Meta_etaStructReduce(v_e_3568_, v_p_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3576_, lean_object* v___x_3577_, lean_object* v_pre_3578_, lean_object* v_post_3579_, uint8_t v_usedLetOnly_3580_, uint8_t v_skipConstInApp_3581_, uint8_t v_skipInstances_3582_, lean_object* v___x_3583_, lean_object* v_inst_3584_, lean_object* v_R_3585_, lean_object* v_a_3586_, lean_object* v_b_3587_, lean_object* v_c_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3576_, v___x_3577_, v_pre_3578_, v_post_3579_, v_usedLetOnly_3580_, v_skipConstInApp_3581_, v_skipInstances_3582_, v_a_3586_, v_b_3587_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3596_ = _args[0];
lean_object* v___x_3597_ = _args[1];
lean_object* v_pre_3598_ = _args[2];
lean_object* v_post_3599_ = _args[3];
lean_object* v_usedLetOnly_3600_ = _args[4];
lean_object* v_skipConstInApp_3601_ = _args[5];
lean_object* v_skipInstances_3602_ = _args[6];
lean_object* v___x_3603_ = _args[7];
lean_object* v_inst_3604_ = _args[8];
lean_object* v_R_3605_ = _args[9];
lean_object* v_a_3606_ = _args[10];
lean_object* v_b_3607_ = _args[11];
lean_object* v_c_3608_ = _args[12];
lean_object* v___y_3609_ = _args[13];
lean_object* v___y_3610_ = _args[14];
lean_object* v___y_3611_ = _args[15];
lean_object* v___y_3612_ = _args[16];
lean_object* v___y_3613_ = _args[17];
lean_object* v___y_3614_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3615_; uint8_t v_skipConstInApp_boxed_3616_; uint8_t v_skipInstances_boxed_3617_; lean_object* v_res_3618_; 
v_usedLetOnly_boxed_3615_ = lean_unbox(v_usedLetOnly_3600_);
v_skipConstInApp_boxed_3616_ = lean_unbox(v_skipConstInApp_3601_);
v_skipInstances_boxed_3617_ = lean_unbox(v_skipInstances_3602_);
v_res_3618_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3596_, v___x_3597_, v_pre_3598_, v_post_3599_, v_usedLetOnly_boxed_3615_, v_skipConstInApp_boxed_3616_, v_skipInstances_boxed_3617_, v___x_3603_, v_inst_3604_, v_R_3605_, v_a_3606_, v_b_3607_, v_c_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec(v___x_3603_);
lean_dec_ref(v___x_3597_);
lean_dec(v_upperBound_3596_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3619_, lean_object* v_m_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3620_, v_a_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3623_, lean_object* v_m_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3623_, v_m_3624_, v_a_3625_);
lean_dec_ref(v_a_3625_);
lean_dec_ref(v_m_3624_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3627_, lean_object* v_name_3628_, uint8_t v_bi_3629_, lean_object* v_type_3630_, lean_object* v_k_3631_, uint8_t v_kind_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3628_, v_bi_3629_, v_type_3630_, v_k_3631_, v_kind_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3640_, lean_object* v_name_3641_, lean_object* v_bi_3642_, lean_object* v_type_3643_, lean_object* v_k_3644_, lean_object* v_kind_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
uint8_t v_bi_boxed_3652_; uint8_t v_kind_boxed_3653_; lean_object* v_res_3654_; 
v_bi_boxed_3652_ = lean_unbox(v_bi_3642_);
v_kind_boxed_3653_ = lean_unbox(v_kind_3645_);
v_res_3654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3640_, v_name_3641_, v_bi_boxed_3652_, v_type_3643_, v_k_3644_, v_kind_boxed_3653_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3655_, lean_object* v_name_3656_, lean_object* v_type_3657_, lean_object* v_val_3658_, lean_object* v_k_3659_, uint8_t v_nondep_3660_, uint8_t v_kind_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3656_, v_type_3657_, v_val_3658_, v_k_3659_, v_nondep_3660_, v_kind_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_name_3670_, lean_object* v_type_3671_, lean_object* v_val_3672_, lean_object* v_k_3673_, lean_object* v_nondep_3674_, lean_object* v_kind_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_nondep_boxed_3682_; uint8_t v_kind_boxed_3683_; lean_object* v_res_3684_; 
v_nondep_boxed_3682_ = lean_unbox(v_nondep_3674_);
v_kind_boxed_3683_ = lean_unbox(v_kind_3675_);
v_res_3684_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3669_, v_name_3670_, v_type_3671_, v_val_3672_, v_k_3673_, v_nondep_boxed_3682_, v_kind_boxed_3683_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3685_, lean_object* v_ref_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3686_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_ref_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3693_, v_ref_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3701_, lean_object* v_x_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_x_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3710_, v_x_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3719_, lean_object* v_m_3720_, lean_object* v_a_3721_, lean_object* v_b_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3720_, v_a_3721_, v_b_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3724_, lean_object* v_a_3725_, lean_object* v_x_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3725_, v_x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3728_, lean_object* v_a_3729_, lean_object* v_x_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3728_, v_a_3729_, v_x_3730_);
lean_dec(v_x_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3731_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3732_, lean_object* v_a_3733_, lean_object* v_x_3734_){
_start:
{
uint8_t v___x_3735_; 
v___x_3735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3733_, v_x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3736_, lean_object* v_a_3737_, lean_object* v_x_3738_){
_start:
{
uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_res_3739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3736_, v_a_3737_, v_x_3738_);
lean_dec(v_x_3738_);
lean_dec_ref(v_a_3737_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3741_, lean_object* v_data_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3744_, lean_object* v_a_3745_, lean_object* v_b_3746_, lean_object* v_x_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3745_, v_b_3746_, v_x_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3749_, lean_object* v_i_3750_, lean_object* v_source_3751_, lean_object* v_target_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3750_, v_source_3751_, v_target_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3754_, lean_object* v_x_3755_, lean_object* v_x_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3755_, v_x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3758_, lean_object* v_inst_3759_, lean_object* v_toBind_3760_, lean_object* v___f_3761_, lean_object* v_____do__lift_3762_){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3763_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3763_, 0, v_____do__lift_3762_);
lean_closure_set(v___x_3763_, 1, v_binderType_3758_);
v___x_3764_ = lean_apply_2(v_inst_3759_, lean_box(0), v___x_3763_);
v___x_3765_ = lean_apply_4(v_toBind_3760_, lean_box(0), lean_box(0), v___x_3764_, v___f_3761_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3766_, lean_object* v_usedFields_3767_, lean_object* v_binderName_3768_, lean_object* v_body_3769_, lean_object* v_val_3770_, lean_object* v_inst_3771_, lean_object* v_inst_3772_, lean_object* v_fieldVal_x3f_3773_, lean_object* v_____do__lift_3774_){
_start:
{
uint8_t v_____do__lift_291__boxed_3775_; lean_object* v_res_3776_; 
v_____do__lift_291__boxed_3775_ = lean_unbox(v_____do__lift_3774_);
v_res_3776_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3766_, v_usedFields_3767_, v_binderName_3768_, v_body_3769_, v_val_3770_, v_inst_3771_, v_inst_3772_, v_fieldVal_x3f_3773_, v_____do__lift_291__boxed_3775_);
lean_dec_ref(v_val_3770_);
lean_dec_ref(v_body_3769_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3777_, lean_object* v_usedFields_3778_, lean_object* v_binderName_3779_, lean_object* v_body_3780_, lean_object* v_inst_3781_, lean_object* v_inst_3782_, lean_object* v_fieldVal_x3f_3783_, lean_object* v_binderType_3784_, lean_object* v_toBind_3785_, lean_object* v_____x_3786_){
_start:
{
if (lean_obj_tag(v_____x_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___f_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_val_3787_ = lean_ctor_get(v_____x_3786_, 0);
lean_inc_n(v_val_3787_, 2);
lean_dec_ref_known(v_____x_3786_, 1);
lean_inc_n(v_inst_3782_, 2);
v___f_3788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3788_, 0, v_toPure_3777_);
lean_closure_set(v___f_3788_, 1, v_usedFields_3778_);
lean_closure_set(v___f_3788_, 2, v_binderName_3779_);
lean_closure_set(v___f_3788_, 3, v_body_3780_);
lean_closure_set(v___f_3788_, 4, v_val_3787_);
lean_closure_set(v___f_3788_, 5, v_inst_3781_);
lean_closure_set(v___f_3788_, 6, v_inst_3782_);
lean_closure_set(v___f_3788_, 7, v_fieldVal_x3f_3783_);
lean_inc(v_toBind_3785_);
v___f_3789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3789_, 0, v_binderType_3784_);
lean_closure_set(v___f_3789_, 1, v_inst_3782_);
lean_closure_set(v___f_3789_, 2, v_toBind_3785_);
lean_closure_set(v___f_3789_, 3, v___f_3788_);
v___x_3790_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3790_, 0, v_val_3787_);
v___x_3791_ = lean_apply_2(v_inst_3782_, lean_box(0), v___x_3790_);
v___x_3792_ = lean_apply_4(v_toBind_3785_, lean_box(0), lean_box(0), v___x_3791_, v___f_3789_);
return v___x_3792_;
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v_____x_3786_);
lean_dec(v_toBind_3785_);
lean_dec_ref(v_binderType_3784_);
lean_dec(v_fieldVal_x3f_3783_);
lean_dec(v_inst_3782_);
lean_dec_ref(v_inst_3781_);
lean_dec_ref(v_body_3780_);
lean_dec(v_binderName_3779_);
lean_dec(v_usedFields_3778_);
v___x_3793_ = lean_box(0);
v___x_3794_ = lean_apply_2(v_toPure_3777_, lean_box(0), v___x_3793_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3798_, lean_object* v_inst_3799_, lean_object* v_fieldVal_x3f_3800_, lean_object* v_usedFields_3801_, lean_object* v_e_3802_){
_start:
{
lean_object* v_toApplicative_3803_; lean_object* v_toBind_3804_; lean_object* v_toPure_3805_; 
v_toApplicative_3803_ = lean_ctor_get(v_inst_3798_, 0);
v_toBind_3804_ = lean_ctor_get(v_inst_3798_, 1);
v_toPure_3805_ = lean_ctor_get(v_toApplicative_3803_, 1);
lean_inc(v_toPure_3805_);
if (lean_obj_tag(v_e_3802_) == 6)
{
lean_object* v_binderName_3810_; lean_object* v_binderType_3811_; lean_object* v_body_3812_; lean_object* v___f_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_inc_n(v_toBind_3804_, 2);
v_binderName_3810_ = lean_ctor_get(v_e_3802_, 0);
lean_inc_n(v_binderName_3810_, 2);
v_binderType_3811_ = lean_ctor_get(v_e_3802_, 1);
lean_inc_ref(v_binderType_3811_);
v_body_3812_ = lean_ctor_get(v_e_3802_, 2);
lean_inc_ref(v_body_3812_);
lean_dec_ref_known(v_e_3802_, 3);
lean_inc(v_fieldVal_x3f_3800_);
v___f_3813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3813_, 0, v_toPure_3805_);
lean_closure_set(v___f_3813_, 1, v_usedFields_3801_);
lean_closure_set(v___f_3813_, 2, v_binderName_3810_);
lean_closure_set(v___f_3813_, 3, v_body_3812_);
lean_closure_set(v___f_3813_, 4, v_inst_3798_);
lean_closure_set(v___f_3813_, 5, v_inst_3799_);
lean_closure_set(v___f_3813_, 6, v_fieldVal_x3f_3800_);
lean_closure_set(v___f_3813_, 7, v_binderType_3811_);
lean_closure_set(v___f_3813_, 8, v_toBind_3804_);
v___x_3814_ = lean_apply_1(v_fieldVal_x3f_3800_, v_binderName_3810_);
v___x_3815_ = lean_apply_4(v_toBind_3804_, lean_box(0), lean_box(0), v___x_3814_, v___f_3813_);
return v___x_3815_;
}
else
{
lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v_fieldVal_x3f_3800_);
lean_dec(v_inst_3799_);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_inst_3798_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; lean_object* v_unused_3834_; 
v_unused_3833_ = lean_ctor_get(v_inst_3798_, 1);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_inst_3798_, 0);
lean_dec(v_unused_3834_);
v___x_3817_ = v_inst_3798_;
v_isShared_3818_ = v_isSharedCheck_3832_;
goto v_resetjp_3816_;
}
else
{
lean_dec(v_inst_3798_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3832_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; uint8_t v___x_3820_; 
lean_inc_ref(v_e_3802_);
v___x_3819_ = l_Lean_Expr_cleanupAnnotations(v_e_3802_);
v___x_3820_ = l_Lean_Expr_isApp(v___x_3819_);
if (v___x_3820_ == 0)
{
lean_dec_ref(v___x_3819_);
lean_del_object(v___x_3817_);
goto v___jp_3806_;
}
else
{
lean_object* v_arg_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_arg_3821_ = lean_ctor_get(v___x_3819_, 1);
lean_inc_ref(v_arg_3821_);
v___x_3822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3819_);
v___x_3823_ = l_Lean_Expr_isApp(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_dec_ref(v___x_3822_);
lean_dec_ref(v_arg_3821_);
lean_del_object(v___x_3817_);
goto v___jp_3806_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3822_);
v___x_3825_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3826_ = l_Lean_Expr_isConstOf(v___x_3824_, v___x_3825_);
lean_dec_ref(v___x_3824_);
if (v___x_3826_ == 0)
{
lean_dec_ref(v_arg_3821_);
lean_del_object(v___x_3817_);
goto v___jp_3806_;
}
else
{
lean_object* v___x_3828_; 
lean_dec_ref(v_e_3802_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set(v___x_3817_, 1, v_arg_3821_);
lean_ctor_set(v___x_3817_, 0, v_usedFields_3801_);
v___x_3828_ = v___x_3817_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_usedFields_3801_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_arg_3821_);
v___x_3828_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
v___x_3830_ = lean_apply_2(v_toPure_3805_, lean_box(0), v___x_3829_);
return v___x_3830_;
}
}
}
}
}
}
v___jp_3806_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_usedFields_3801_);
lean_ctor_set(v___x_3807_, 1, v_e_3802_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
v___x_3809_ = lean_apply_2(v_toPure_3805_, lean_box(0), v___x_3808_);
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3835_, lean_object* v_usedFields_3836_, lean_object* v_binderName_3837_, lean_object* v_body_3838_, lean_object* v_val_3839_, lean_object* v_inst_3840_, lean_object* v_inst_3841_, lean_object* v_fieldVal_x3f_3842_, uint8_t v_____do__lift_3843_){
_start:
{
if (v_____do__lift_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec(v_fieldVal_x3f_3842_);
lean_dec(v_inst_3841_);
lean_dec_ref(v_inst_3840_);
lean_dec(v_binderName_3837_);
lean_dec(v_usedFields_3836_);
v___x_3844_ = lean_box(0);
v___x_3845_ = lean_apply_2(v_toPure_3835_, lean_box(0), v___x_3844_);
return v___x_3845_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_dec(v_toPure_3835_);
v___x_3846_ = l_Lean_NameSet_insert(v_usedFields_3836_, v_binderName_3837_);
v___x_3847_ = lean_expr_instantiate1(v_body_3838_, v_val_3839_);
v___x_3848_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3840_, v_inst_3841_, v_fieldVal_x3f_3842_, v___x_3846_, v___x_3847_);
return v___x_3848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3849_, lean_object* v_inst_3850_, lean_object* v_inst_3851_, lean_object* v_fieldVal_x3f_3852_, lean_object* v_usedFields_3853_, lean_object* v_e_3854_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3850_, v_inst_3851_, v_fieldVal_x3f_3852_, v_usedFields_3853_, v_e_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3856_, lean_object* v_inst_3857_, lean_object* v_fieldVal_x3f_3858_, lean_object* v_toPure_3859_, lean_object* v_____s_3860_){
_start:
{
lean_object* v_fst_3861_; 
v_fst_3861_ = lean_ctor_get(v_____s_3860_, 0);
if (lean_obj_tag(v_fst_3861_) == 0)
{
lean_object* v_snd_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec(v_toPure_3859_);
v_snd_3862_ = lean_ctor_get(v_____s_3860_, 1);
lean_inc(v_snd_3862_);
lean_dec_ref(v_____s_3860_);
v___x_3863_ = l_Lean_NameSet_empty;
v___x_3864_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3856_, v_inst_3857_, v_fieldVal_x3f_3858_, v___x_3863_, v_snd_3862_);
return v___x_3864_;
}
else
{
lean_object* v_val_3865_; lean_object* v___x_3866_; 
lean_inc_ref(v_fst_3861_);
lean_dec_ref(v_____s_3860_);
lean_dec(v_fieldVal_x3f_3858_);
lean_dec(v_inst_3857_);
lean_dec_ref(v_inst_3856_);
v_val_3865_ = lean_ctor_get(v_fst_3861_, 0);
lean_inc(v_val_3865_);
lean_dec_ref_known(v_fst_3861_, 1);
v___x_3866_ = lean_apply_2(v_toPure_3859_, lean_box(0), v_val_3865_);
return v___x_3866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3867_, lean_object* v_a_3868_, lean_object* v___x_3869_, lean_object* v_toPure_3870_, lean_object* v_____r_3871_){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3872_ = lean_expr_instantiate1(v_body_3867_, v_a_3868_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3869_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = lean_apply_2(v_toPure_3870_, lean_box(0), v___x_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3876_, lean_object* v_a_3877_, lean_object* v___x_3878_, lean_object* v_toPure_3879_, lean_object* v_____r_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3876_, v_a_3877_, v___x_3878_, v_toPure_3879_, v_____r_3880_);
lean_dec_ref(v_a_3877_);
lean_dec_ref(v_body_3876_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3884_, lean_object* v_toPure_3885_, lean_object* v___f_3886_, uint8_t v_____do__lift_3887_){
_start:
{
if (v_____do__lift_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec(v___f_3886_);
v___x_3888_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v_snd_3884_);
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
v___x_3891_ = lean_apply_2(v_toPure_3885_, lean_box(0), v___x_3890_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec(v_toPure_3885_);
lean_dec(v_snd_3884_);
v___x_3892_ = lean_box(0);
v___x_3893_ = lean_apply_1(v___f_3886_, v___x_3892_);
return v___x_3893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3894_, lean_object* v_toPure_3895_, lean_object* v___f_3896_, lean_object* v_____do__lift_3897_){
_start:
{
uint8_t v_____do__lift_566__boxed_3898_; lean_object* v_res_3899_; 
v_____do__lift_566__boxed_3898_ = lean_unbox(v_____do__lift_3897_);
v_res_3899_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3894_, v_toPure_3895_, v___f_3896_, v_____do__lift_566__boxed_3898_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3900_, lean_object* v_inst_3901_, lean_object* v_toBind_3902_, lean_object* v___f_3903_, lean_object* v_____do__lift_3904_){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3905_, 0, v_____do__lift_3904_);
lean_closure_set(v___x_3905_, 1, v_binderType_3900_);
v___x_3906_ = lean_apply_2(v_inst_3901_, lean_box(0), v___x_3905_);
v___x_3907_ = lean_apply_4(v_toBind_3902_, lean_box(0), lean_box(0), v___x_3906_, v___f_3903_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3908_, lean_object* v_toPure_3909_, lean_object* v_levels_x3f_3910_, lean_object* v_inst_3911_, lean_object* v_toBind_3912_, lean_object* v_a_3913_, lean_object* v_x_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_snd_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3936_; 
v_snd_3916_ = lean_ctor_get(v___y_3915_, 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___y_3915_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v___y_3915_, 0);
lean_dec(v_unused_3937_);
v___x_3918_ = v___y_3915_;
v_isShared_3919_ = v_isSharedCheck_3936_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_snd_3916_);
lean_dec(v___y_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3936_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
if (lean_obj_tag(v_snd_3916_) == 6)
{
lean_object* v_binderType_3920_; lean_object* v_body_3921_; lean_object* v___f_3922_; 
lean_del_object(v___x_3918_);
v_binderType_3920_ = lean_ctor_get(v_snd_3916_, 1);
lean_inc_ref(v_binderType_3920_);
v_body_3921_ = lean_ctor_get(v_snd_3916_, 2);
lean_inc(v_toPure_3909_);
lean_inc(v___x_3908_);
lean_inc_ref(v_a_3913_);
lean_inc_ref(v_body_3921_);
v___f_3922_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3922_, 0, v_body_3921_);
lean_closure_set(v___f_3922_, 1, v_a_3913_);
lean_closure_set(v___f_3922_, 2, v___x_3908_);
lean_closure_set(v___f_3922_, 3, v_toPure_3909_);
if (lean_obj_tag(v_levels_x3f_3910_) == 0)
{
lean_object* v___f_3923_; lean_object* v___f_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_dec(v___x_3908_);
v___f_3923_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3923_, 0, v_snd_3916_);
lean_closure_set(v___f_3923_, 1, v_toPure_3909_);
lean_closure_set(v___f_3923_, 2, v___f_3922_);
lean_inc(v_toBind_3912_);
lean_inc(v_inst_3911_);
v___f_3924_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3924_, 0, v_binderType_3920_);
lean_closure_set(v___f_3924_, 1, v_inst_3911_);
lean_closure_set(v___f_3924_, 2, v_toBind_3912_);
lean_closure_set(v___f_3924_, 3, v___f_3923_);
v___x_3925_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3925_, 0, v_a_3913_);
v___x_3926_ = lean_apply_2(v_inst_3911_, lean_box(0), v___x_3925_);
v___x_3927_ = lean_apply_4(v_toBind_3912_, lean_box(0), lean_box(0), v___x_3926_, v___f_3924_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_inc_ref(v_body_3921_);
lean_dec_ref(v___f_3922_);
lean_dec_ref(v_binderType_3920_);
lean_dec_ref_known(v_snd_3916_, 3);
lean_dec(v_toBind_3912_);
lean_dec(v_inst_3911_);
v___x_3928_ = lean_box(0);
v___x_3929_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3921_, v_a_3913_, v___x_3908_, v_toPure_3909_, v___x_3928_);
lean_dec_ref(v_a_3913_);
lean_dec_ref(v_body_3921_);
return v___x_3929_;
}
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3932_; 
lean_dec_ref(v_a_3913_);
lean_dec(v_toBind_3912_);
lean_dec(v_inst_3911_);
lean_dec(v___x_3908_);
v___x_3930_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 0, v___x_3930_);
v___x_3932_ = v___x_3918_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_snd_3916_);
v___x_3932_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
v___x_3934_ = lean_apply_2(v_toPure_3909_, lean_box(0), v___x_3933_);
return v___x_3934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3938_, lean_object* v_toPure_3939_, lean_object* v_levels_x3f_3940_, lean_object* v_inst_3941_, lean_object* v_toBind_3942_, lean_object* v_a_3943_, lean_object* v_x_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3938_, v_toPure_3939_, v_levels_x3f_3940_, v_inst_3941_, v_toBind_3942_, v_a_3943_, v_x_3944_, v___y_3945_);
lean_dec(v_levels_x3f_3940_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3947_, lean_object* v_levels_x3f_3948_, lean_object* v_inst_3949_, lean_object* v_toBind_3950_, lean_object* v_params_3951_, lean_object* v_inst_3952_, lean_object* v___f_3953_, lean_object* v_val_3954_){
_start:
{
lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; size_t v_sz_3958_; size_t v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3955_ = lean_box(0);
lean_inc(v_toBind_3950_);
v___f_3956_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3956_, 0, v___x_3955_);
lean_closure_set(v___f_3956_, 1, v_toPure_3947_);
lean_closure_set(v___f_3956_, 2, v_levels_x3f_3948_);
lean_closure_set(v___f_3956_, 3, v_inst_3949_);
lean_closure_set(v___f_3956_, 4, v_toBind_3950_);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v_val_3954_);
v_sz_3958_ = lean_array_size(v_params_3951_);
v___x_3959_ = ((size_t)0ULL);
v___x_3960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3952_, v_params_3951_, v___f_3956_, v_sz_3958_, v___x_3959_, v___x_3957_);
v___x_3961_ = lean_apply_4(v_toBind_3950_, lean_box(0), lean_box(0), v___x_3960_, v___f_3953_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3962_, lean_object* v_us_3963_, uint8_t v___x_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3962_, v_us_3963_, v___x_3964_, v___y_3967_, v___y_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3971_, lean_object* v_us_3972_, lean_object* v___x_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
uint8_t v___x_677__boxed_3979_; lean_object* v_res_3980_; 
v___x_677__boxed_3979_ = lean_unbox(v___x_3973_);
v_res_3980_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3971_, v_us_3972_, v___x_677__boxed_3979_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v_cinfo_3971_);
return v_res_3980_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3984_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_3985_ = lean_unsigned_to_nat(2u);
v___x_3986_ = lean_unsigned_to_nat(202u);
v___x_3987_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_3988_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_3989_ = l_mkPanicMessageWithDecl(v___x_3988_, v___x_3987_, v___x_3986_, v___x_3985_, v___x_3984_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_3990_, lean_object* v___x_3991_, lean_object* v_inst_3992_, lean_object* v_toBind_3993_, lean_object* v___f_3994_, lean_object* v_us_3995_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3996_ = l_List_lengthTR___redArg(v_us_3995_);
v___x_3997_ = l_Lean_ConstantInfo_levelParams(v_cinfo_3990_);
v___x_3998_ = l_List_lengthTR___redArg(v___x_3997_);
lean_dec(v___x_3997_);
v___x_3999_ = lean_nat_dec_eq(v___x_3996_, v___x_3998_);
lean_dec(v___x_3998_);
lean_dec(v___x_3996_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec(v_us_3995_);
lean_dec(v___f_3994_);
lean_dec(v_toBind_3993_);
lean_dec(v_inst_3992_);
lean_dec_ref(v_cinfo_3990_);
v___x_4000_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4001_ = l_panic___redArg(v___x_3991_, v___x_4000_);
return v___x_4001_;
}
else
{
uint8_t v___x_4002_; lean_object* v___x_4003_; lean_object* v___f_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4002_ = 0;
v___x_4003_ = lean_box(v___x_4002_);
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4004_, 0, v_cinfo_3990_);
lean_closure_set(v___f_4004_, 1, v_us_3995_);
lean_closure_set(v___f_4004_, 2, v___x_4003_);
v___x_4005_ = lean_apply_2(v_inst_3992_, lean_box(0), v___f_4004_);
v___x_4006_ = lean_apply_4(v_toBind_3993_, lean_box(0), lean_box(0), v___x_4005_, v___f_3994_);
return v___x_4006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4007_, lean_object* v___x_4008_, lean_object* v_inst_4009_, lean_object* v_toBind_4010_, lean_object* v___f_4011_, lean_object* v_us_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4007_, v___x_4008_, v_inst_4009_, v_toBind_4010_, v___f_4011_, v_us_4012_);
lean_dec(v___x_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4014_, lean_object* v_inst_4015_, lean_object* v_toBind_4016_, lean_object* v___f_4017_, lean_object* v_levels_x3f_4018_, lean_object* v_toPure_4019_, lean_object* v_cinfo_4020_){
_start:
{
lean_object* v___f_4021_; 
lean_inc(v_toBind_4016_);
lean_inc(v_inst_4015_);
lean_inc_ref(v_cinfo_4020_);
v___f_4021_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4021_, 0, v_cinfo_4020_);
lean_closure_set(v___f_4021_, 1, v___x_4014_);
lean_closure_set(v___f_4021_, 2, v_inst_4015_);
lean_closure_set(v___f_4021_, 3, v_toBind_4016_);
lean_closure_set(v___f_4021_, 4, v___f_4017_);
if (lean_obj_tag(v_levels_x3f_4018_) == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
lean_dec(v_toPure_4019_);
v___x_4022_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4022_, 0, v_cinfo_4020_);
v___x_4023_ = lean_apply_2(v_inst_4015_, lean_box(0), v___x_4022_);
v___x_4024_ = lean_apply_4(v_toBind_4016_, lean_box(0), lean_box(0), v___x_4023_, v___f_4021_);
return v___x_4024_;
}
else
{
lean_object* v_val_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
lean_dec_ref(v_cinfo_4020_);
lean_dec(v_inst_4015_);
v_val_4025_ = lean_ctor_get(v_levels_x3f_4018_, 0);
lean_inc(v_val_4025_);
lean_dec_ref_known(v_levels_x3f_4018_, 1);
v___x_4026_ = lean_apply_2(v_toPure_4019_, lean_box(0), v_val_4025_);
v___x_4027_ = lean_apply_4(v_toBind_4016_, lean_box(0), lean_box(0), v___x_4026_, v___f_4021_);
return v___x_4027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4028_, lean_object* v_inst_4029_, lean_object* v_inst_4030_, lean_object* v_inst_4031_, lean_object* v_defaultFn_4032_, lean_object* v_levels_x3f_4033_, lean_object* v_params_4034_, lean_object* v_fieldVal_x3f_4035_){
_start:
{
lean_object* v_toApplicative_4036_; lean_object* v_toBind_4037_; lean_object* v_toPure_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___f_4041_; lean_object* v___f_4042_; lean_object* v___x_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; 
v_toApplicative_4036_ = lean_ctor_get(v_inst_4028_, 0);
v_toBind_4037_ = lean_ctor_get(v_inst_4028_, 1);
lean_inc_n(v_toBind_4037_, 3);
v_toPure_4038_ = lean_ctor_get(v_toApplicative_4036_, 1);
lean_inc_n(v_toPure_4038_, 3);
v___x_4039_ = lean_box(0);
lean_inc_ref_n(v_inst_4028_, 3);
v___x_4040_ = l_Lean_getConstInfo___redArg(v_inst_4028_, v_inst_4029_, v_inst_4030_, v_defaultFn_4032_);
lean_inc_n(v_inst_4031_, 2);
v___f_4041_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4041_, 0, v_inst_4028_);
lean_closure_set(v___f_4041_, 1, v_inst_4031_);
lean_closure_set(v___f_4041_, 2, v_fieldVal_x3f_4035_);
lean_closure_set(v___f_4041_, 3, v_toPure_4038_);
lean_inc(v_levels_x3f_4033_);
v___f_4042_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4042_, 0, v_toPure_4038_);
lean_closure_set(v___f_4042_, 1, v_levels_x3f_4033_);
lean_closure_set(v___f_4042_, 2, v_inst_4031_);
lean_closure_set(v___f_4042_, 3, v_toBind_4037_);
lean_closure_set(v___f_4042_, 4, v_params_4034_);
lean_closure_set(v___f_4042_, 5, v_inst_4028_);
lean_closure_set(v___f_4042_, 6, v___f_4041_);
v___x_4043_ = l_instInhabitedOfMonad___redArg(v_inst_4028_, v___x_4039_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4044_, 0, v___x_4043_);
lean_closure_set(v___f_4044_, 1, v_inst_4031_);
lean_closure_set(v___f_4044_, 2, v_toBind_4037_);
lean_closure_set(v___f_4044_, 3, v___f_4042_);
lean_closure_set(v___f_4044_, 4, v_levels_x3f_4033_);
lean_closure_set(v___f_4044_, 5, v_toPure_4038_);
v___x_4045_ = lean_apply_4(v_toBind_4037_, lean_box(0), lean_box(0), v___x_4040_, v___f_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4046_, lean_object* v_inst_4047_, lean_object* v_inst_4048_, lean_object* v_inst_4049_, lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_defaultFn_4052_, lean_object* v_levels_x3f_4053_, lean_object* v_params_4054_, lean_object* v_fieldVal_x3f_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4047_, v_inst_4048_, v_inst_4049_, v_inst_4050_, v_defaultFn_4052_, v_levels_x3f_4053_, v_params_4054_, v_fieldVal_x3f_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4057_, lean_object* v_inst_4058_, lean_object* v_inst_4059_, lean_object* v_inst_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_, lean_object* v_defaultFn_4063_, lean_object* v_levels_x3f_4064_, lean_object* v_params_4065_, lean_object* v_fieldVal_x3f_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4057_, v_inst_4058_, v_inst_4059_, v_inst_4060_, v_inst_4061_, v_inst_4062_, v_defaultFn_4063_, v_levels_x3f_4064_, v_params_4065_, v_fieldVal_x3f_4066_);
lean_dec_ref(v_inst_4062_);
return v_res_4067_;
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
