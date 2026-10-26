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
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__2));
v___x_55_ = l_Lean_stringToMessageData(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__5(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__4));
v___x_58_ = l_Lean_stringToMessageData(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName(lean_object* v_struct_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Expr_getAppFn(v_struct_59_);
if (lean_obj_tag(v___x_65_) == 4)
{
lean_object* v_declName_66_; lean_object* v___x_67_; lean_object* v_env_68_; uint8_t v___x_69_; 
v_declName_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc_n(v_declName_66_, 2);
lean_dec_ref_known(v___x_65_, 2);
v___x_67_ = lean_st_ref_get(v_a_63_);
v_env_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_ref(v_env_68_);
lean_dec(v___x_67_);
v___x_69_ = l_Lean_isStructure(v_env_68_, v_declName_66_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v___x_70_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_71_ = l_Lean_MessageData_ofConstName(v_declName_66_, v___x_69_);
v___x_72_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__3, &l_Lean_Meta_getStructureName___closed__3_once, _init_l_Lean_Meta_getStructureName___closed__3);
v___x_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_74_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_object* v___x_84_; 
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v_declName_66_);
return v___x_84_;
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec_ref(v___x_65_);
v___x_85_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__5, &l_Lean_Meta_getStructureName___closed__5_once, _init_l_Lean_Meta_getStructureName___closed__5);
v___x_86_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_85_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName___boxed(lean_object* v_struct_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_getStructureName(v_struct_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec_ref(v_struct_87_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_object* v_00_u03b1_94_, lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(lean_object* v_00_u03b1_102_, lean_object* v_msg_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(v_00_u03b1_102_, v_msg_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(lean_object* v_name_110_, lean_object* v_levelParams_111_, lean_object* v_type_112_, lean_object* v_value_113_, lean_object* v_hints_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; uint8_t v___y_119_; lean_object* v_env_127_; uint8_t v___x_128_; 
v___x_117_ = lean_st_ref_get(v___y_115_);
v_env_127_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref_n(v_env_127_, 2);
lean_dec(v___x_117_);
v___x_128_ = l_Lean_Environment_hasUnsafe(v_env_127_, v_type_112_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = l_Lean_Environment_hasUnsafe(v_env_127_, v_value_113_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 1;
v___y_119_ = v___x_130_;
goto v___jp_118_;
}
else
{
goto v___jp_125_;
}
}
else
{
lean_dec_ref(v_env_127_);
goto v___jp_125_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_inc(v_name_110_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v_name_110_);
lean_ctor_set(v___x_120_, 1, v_levelParams_111_);
lean_ctor_set(v___x_120_, 2, v_type_112_);
v___x_121_ = lean_box(0);
v___x_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_122_, 0, v_name_110_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_123_, 0, v___x_120_);
lean_ctor_set(v___x_123_, 1, v_value_113_);
lean_ctor_set(v___x_123_, 2, v_hints_114_);
lean_ctor_set(v___x_123_, 3, v___x_122_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*4, v___y_119_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
v___jp_125_:
{
uint8_t v___x_126_; 
v___x_126_ = 0;
v___y_119_ = v___x_126_;
goto v___jp_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v_name_131_, lean_object* v_levelParams_132_, lean_object* v_type_133_, lean_object* v_value_134_, lean_object* v_hints_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_131_, v_levelParams_132_, v_type_133_, v_value_134_, v_hints_135_, v___y_136_);
lean_dec(v___y_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_name_139_, lean_object* v_levelParams_140_, lean_object* v_type_141_, lean_object* v_value_142_, lean_object* v_hints_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_139_, v_levelParams_140_, v_type_141_, v_value_142_, v_hints_143_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object* v_name_150_, lean_object* v_levelParams_151_, lean_object* v_type_152_, lean_object* v_value_153_, lean_object* v_hints_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_150_, v_levelParams_151_, v_type_152_, v_value_153_, v_hints_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v_k_161_, lean_object* v_b_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; 
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
v___x_168_ = lean_apply_6(v_k_161_, v_b_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, lean_box(0));
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_169_, lean_object* v_b_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_169_, v_b_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_name_177_, uint8_t v_bi_178_, lean_object* v_type_179_, lean_object* v_k_180_, uint8_t v_kind_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_187_, 0, v_k_180_);
v___x_188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_177_, v_bi_178_, v_type_179_, v___f_187_, v_kind_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_188_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_188_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object* v_name_205_, lean_object* v_bi_206_, lean_object* v_type_207_, lean_object* v_k_208_, lean_object* v_kind_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v_bi_boxed_215_; uint8_t v_kind_boxed_216_; lean_object* v_res_217_; 
v_bi_boxed_215_ = lean_unbox(v_bi_206_);
v_kind_boxed_216_ = lean_unbox(v_kind_209_);
v_res_217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_205_, v_bi_boxed_215_, v_type_207_, v_k_208_, v_kind_boxed_216_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_00_u03b1_218_, lean_object* v_name_219_, uint8_t v_bi_220_, lean_object* v_type_221_, lean_object* v_k_222_, uint8_t v_kind_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_219_, v_bi_220_, v_type_221_, v_k_222_, v_kind_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object* v_00_u03b1_230_, lean_object* v_name_231_, lean_object* v_bi_232_, lean_object* v_type_233_, lean_object* v_k_234_, lean_object* v_kind_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_bi_boxed_241_; uint8_t v_kind_boxed_242_; lean_object* v_res_243_; 
v_bi_boxed_241_ = lean_unbox(v_bi_232_);
v_kind_boxed_242_ = lean_unbox(v_kind_235_);
v_res_243_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(v_00_u03b1_230_, v_name_231_, v_bi_boxed_241_, v_type_233_, v_k_234_, v_kind_boxed_242_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_244_, lean_object* v_b_245_, lean_object* v_c_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
v___x_252_ = lean_apply_7(v_k_244_, v_b_245_, v_c_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, lean_box(0));
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_253_, lean_object* v_b_254_, lean_object* v_c_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_253_, v_b_254_, v_c_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_type_262_, lean_object* v_maxFVars_x3f_263_, lean_object* v_k_264_, uint8_t v_cleanupAnnotations_265_, uint8_t v_whnfType_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; 
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_272_, 0, v_k_264_);
v___x_273_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_262_, v_maxFVars_x3f_263_, v___f_272_, v_cleanupAnnotations_265_, v_whnfType_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_273_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_273_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_type_290_, lean_object* v_maxFVars_x3f_291_, lean_object* v_k_292_, lean_object* v_cleanupAnnotations_293_, lean_object* v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_300_; uint8_t v_whnfType_boxed_301_; lean_object* v_res_302_; 
v_cleanupAnnotations_boxed_300_ = lean_unbox(v_cleanupAnnotations_293_);
v_whnfType_boxed_301_ = lean_unbox(v_whnfType_294_);
v_res_302_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_290_, v_maxFVars_x3f_291_, v_k_292_, v_cleanupAnnotations_boxed_300_, v_whnfType_boxed_301_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_303_, lean_object* v_type_304_, lean_object* v_maxFVars_x3f_305_, lean_object* v_k_306_, uint8_t v_cleanupAnnotations_307_, uint8_t v_whnfType_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_304_, v_maxFVars_x3f_305_, v_k_306_, v_cleanupAnnotations_307_, v_whnfType_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_315_, lean_object* v_type_316_, lean_object* v_maxFVars_x3f_317_, lean_object* v_k_318_, lean_object* v_cleanupAnnotations_319_, lean_object* v_whnfType_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_326_; uint8_t v_whnfType_boxed_327_; lean_object* v_res_328_; 
v_cleanupAnnotations_boxed_326_ = lean_unbox(v_cleanupAnnotations_319_);
v_whnfType_boxed_327_ = lean_unbox(v_whnfType_320_);
v_res_328_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_315_, v_type_316_, v_maxFVars_x3f_317_, v_k_318_, v_cleanupAnnotations_boxed_326_, v_whnfType_boxed_327_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_lctx_329_, lean_object* v_localInsts_330_, lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_329_, v_localInsts_330_, v_x_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_lctx_354_, lean_object* v_localInsts_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_354_, v_localInsts_355_, v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_363_, lean_object* v_lctx_364_, lean_object* v_localInsts_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_364_, v_localInsts_365_, v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_373_, lean_object* v_lctx_374_, lean_object* v_localInsts_375_, lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_373_, v_lctx_374_, v_localInsts_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_toCold_390_; lean_object* v_currRecDepth_391_; lean_object* v_ref_392_; uint16_t v_optionFlags_393_; uint8_t v_suppressElabErrors_394_; uint8_t v_checkDeprecated_395_; uint8_t v_isRecordingDeps_396_; lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_toCold_390_ = lean_ctor_get(v___y_387_, 0);
v_currRecDepth_391_ = lean_ctor_get(v___y_387_, 1);
v_ref_392_ = lean_ctor_get(v___y_387_, 2);
v_optionFlags_393_ = lean_ctor_get_uint16(v___y_387_, sizeof(void*)*3);
v_suppressElabErrors_394_ = lean_ctor_get_uint8(v___y_387_, sizeof(void*)*3 + 2);
v_checkDeprecated_395_ = lean_ctor_get_uint8(v___y_387_, sizeof(void*)*3 + 3);
v_isRecordingDeps_396_ = lean_ctor_get_uint8(v___y_387_, sizeof(void*)*3 + 4);
v_ref_397_ = l_Lean_replaceRef(v_ref_383_, v_ref_392_);
lean_inc(v_currRecDepth_391_);
lean_inc_ref(v_toCold_390_);
v___x_398_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_398_, 0, v_toCold_390_);
lean_ctor_set(v___x_398_, 1, v_currRecDepth_391_);
lean_ctor_set(v___x_398_, 2, v_ref_397_);
lean_ctor_set_uint16(v___x_398_, sizeof(void*)*3, v_optionFlags_393_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 2, v_suppressElabErrors_394_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 3, v_checkDeprecated_395_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 4, v_isRecordingDeps_396_);
v___x_399_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_384_, v___y_385_, v___y_386_, v___x_398_, v___y_388_);
lean_dec_ref_known(v___x_398_, 3);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_400_, v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v_ref_400_);
return v_res_407_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_417_, lean_object* v_projName_418_, lean_object* v_n_419_, lean_object* v_ref_420_, lean_object* v___f_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
if (v___x_417_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_427_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_428_ = l_Lean_MessageData_ofName(v_projName_418_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_MessageData_ofConstName(v_n_419_, v___x_417_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_420_, v___x_435_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
v___x_438_ = lean_apply_6(v___f_421_, v_a_437_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, lean_box(0));
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v___f_421_);
v_a_439_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_436_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_436_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v_n_419_);
lean_dec(v_projName_418_);
v___x_447_ = lean_box(0);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
v___x_448_ = lean_apply_6(v___f_421_, v___x_447_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, lean_box(0));
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_449_, lean_object* v_projName_450_, lean_object* v_n_451_, lean_object* v_ref_452_, lean_object* v___f_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v___x_17306__boxed_459_; lean_object* v_res_460_; 
v___x_17306__boxed_459_ = lean_unbox(v___x_449_);
v_res_460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17306__boxed_459_, v_projName_450_, v_n_451_, v_ref_452_, v___f_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_ref_452_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_461_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_467_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v___x_466_);
lean_ctor_set(v___x_467_, 4, v___x_466_);
lean_ctor_set(v___x_467_, 5, v___x_466_);
lean_ctor_set(v___x_467_, 6, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_468_, uint8_t v_s_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; lean_object* v_env_474_; lean_object* v_nextMacroScope_475_; lean_object* v_ngen_476_; lean_object* v_auxDeclNGen_477_; lean_object* v_traceState_478_; lean_object* v_recordedDeps_479_; lean_object* v_messages_480_; lean_object* v_infoState_481_; lean_object* v_snapshotTasks_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_511_; 
v___x_473_ = lean_st_ref_take(v___y_471_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
v_nextMacroScope_475_ = lean_ctor_get(v___x_473_, 1);
v_ngen_476_ = lean_ctor_get(v___x_473_, 2);
v_auxDeclNGen_477_ = lean_ctor_get(v___x_473_, 3);
v_traceState_478_ = lean_ctor_get(v___x_473_, 4);
v_recordedDeps_479_ = lean_ctor_get(v___x_473_, 6);
v_messages_480_ = lean_ctor_get(v___x_473_, 7);
v_infoState_481_ = lean_ctor_get(v___x_473_, 8);
v_snapshotTasks_482_ = lean_ctor_get(v___x_473_, 9);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___x_473_, 5);
lean_dec(v_unused_512_);
v___x_484_ = v___x_473_;
v_isShared_485_ = v_isSharedCheck_511_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snapshotTasks_482_);
lean_inc(v_infoState_481_);
lean_inc(v_messages_480_);
lean_inc(v_recordedDeps_479_);
lean_inc(v_traceState_478_);
lean_inc(v_auxDeclNGen_477_);
lean_inc(v_ngen_476_);
lean_inc(v_nextMacroScope_475_);
lean_inc(v_env_474_);
lean_dec(v___x_473_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_511_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_486_ = 0;
v___x_487_ = lean_box(0);
v___x_488_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_474_, v_declName_468_, v_s_469_, v___x_486_, v___x_487_);
v___x_489_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 5, v___x_489_);
lean_ctor_set(v___x_484_, 0, v___x_488_);
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_nextMacroScope_475_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_ngen_476_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_auxDeclNGen_477_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_traceState_478_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_recordedDeps_479_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_messages_480_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_infoState_481_);
lean_ctor_set(v_reuseFailAlloc_510_, 9, v_snapshotTasks_482_);
v___x_491_ = v_reuseFailAlloc_510_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_mctx_494_; lean_object* v_zetaDeltaFVarIds_495_; lean_object* v_postponed_496_; lean_object* v_diag_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_508_; 
v___x_492_ = lean_st_ref_put(v___y_471_, v___x_491_);
v___x_493_ = lean_st_ref_take(v___y_470_);
v_mctx_494_ = lean_ctor_get(v___x_493_, 0);
v_zetaDeltaFVarIds_495_ = lean_ctor_get(v___x_493_, 2);
v_postponed_496_ = lean_ctor_get(v___x_493_, 3);
v_diag_497_ = lean_ctor_get(v___x_493_, 4);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_493_, 1);
lean_dec(v_unused_509_);
v___x_499_ = v___x_493_;
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_diag_497_);
lean_inc(v_postponed_496_);
lean_inc(v_zetaDeltaFVarIds_495_);
lean_inc(v_mctx_494_);
lean_dec(v___x_493_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_508_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_mctx_494_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_zetaDeltaFVarIds_495_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_postponed_496_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_diag_497_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_st_ref_put(v___y_470_, v___x_504_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_501_);
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_513_, lean_object* v_s_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_s_boxed_518_; lean_object* v_res_519_; 
v_s_boxed_518_ = lean_unbox(v_s_514_);
v_res_519_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_513_, v_s_boxed_518_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec(v___y_515_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v___x_526_; lean_object* v___x_527_; 
v___x_526_ = 0;
v___x_527_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_520_, v___x_526_, v___y_522_, v___y_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_534_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_544_, lean_object* v_projName_545_, lean_object* v___x_546_, lean_object* v_a_547_, uint8_t v_instImplicit_548_, lean_object* v___x_549_, lean_object* v_params_550_, lean_object* v_self_551_, lean_object* v_b_552_, uint8_t v___x_553_, lean_object* v_a_554_, lean_object* v___x_555_, lean_object* v_paramInfoOverrides_556_, lean_object* v_n_557_, lean_object* v_ref_558_, lean_object* v___x_559_, uint8_t v_a_560_, lean_object* v_____r_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; uint8_t v___y_631_; uint8_t v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = l_List_lengthTR___redArg(v_paramInfoOverrides_556_);
v___x_731_ = lean_array_get_size(v_params_550_);
v___x_732_ = lean_nat_dec_le(v___x_730_, v___x_731_);
lean_dec(v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_545_);
v___x_734_ = l_Lean_MessageData_ofName(v_projName_545_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
lean_inc(v_n_557_);
v___x_738_ = l_Lean_MessageData_ofConstName(v_n_557_, v___x_732_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_558_, v___x_741_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_dec_ref_known(v___x_742_, 1);
goto v___jp_691_;
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
goto v___jp_691_;
}
v___jp_567_:
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v_nextMacroScope_572_; lean_object* v_ngen_573_; lean_object* v_auxDeclNGen_574_; lean_object* v_traceState_575_; lean_object* v_recordedDeps_576_; lean_object* v_messages_577_; lean_object* v_infoState_578_; lean_object* v_snapshotTasks_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_611_; 
v___x_570_ = lean_st_ref_take(v___y_569_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
v_nextMacroScope_572_ = lean_ctor_get(v___x_570_, 1);
v_ngen_573_ = lean_ctor_get(v___x_570_, 2);
v_auxDeclNGen_574_ = lean_ctor_get(v___x_570_, 3);
v_traceState_575_ = lean_ctor_get(v___x_570_, 4);
v_recordedDeps_576_ = lean_ctor_get(v___x_570_, 6);
v_messages_577_ = lean_ctor_get(v___x_570_, 7);
v_infoState_578_ = lean_ctor_get(v___x_570_, 8);
v_snapshotTasks_579_ = lean_ctor_get(v___x_570_, 9);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_570_, 5);
lean_dec(v_unused_612_);
v___x_581_ = v___x_570_;
v_isShared_582_ = v_isSharedCheck_611_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snapshotTasks_579_);
lean_inc(v_infoState_578_);
lean_inc(v_messages_577_);
lean_inc(v_recordedDeps_576_);
lean_inc(v_traceState_575_);
lean_inc(v_auxDeclNGen_574_);
lean_inc(v_ngen_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_env_571_);
lean_dec(v___x_570_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_611_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_name_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v_name_583_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_name_583_);
lean_dec_ref(v___x_544_);
lean_inc(v_projName_545_);
v___x_584_ = l_Lean_addProjectionFnInfo(v_env_571_, v_projName_545_, v_name_583_, v___x_546_, v_a_547_, v_instImplicit_548_);
v___x_585_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 5, v___x_585_);
lean_ctor_set(v___x_581_, 0, v___x_584_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_ngen_573_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_auxDeclNGen_574_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_traceState_575_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_610_, 6, v_recordedDeps_576_);
lean_ctor_set(v_reuseFailAlloc_610_, 7, v_messages_577_);
lean_ctor_set(v_reuseFailAlloc_610_, 8, v_infoState_578_);
lean_ctor_set(v_reuseFailAlloc_610_, 9, v_snapshotTasks_579_);
v___x_587_ = v_reuseFailAlloc_610_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_mctx_590_; lean_object* v_zetaDeltaFVarIds_591_; lean_object* v_postponed_592_; lean_object* v_diag_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_608_; 
v___x_588_ = lean_st_ref_put(v___y_569_, v___x_587_);
v___x_589_ = lean_st_ref_take(v___y_568_);
v_mctx_590_ = lean_ctor_get(v___x_589_, 0);
v_zetaDeltaFVarIds_591_ = lean_ctor_get(v___x_589_, 2);
v_postponed_592_ = lean_ctor_get(v___x_589_, 3);
v_diag_593_ = lean_ctor_get(v___x_589_, 4);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_589_, 1);
lean_dec(v_unused_609_);
v___x_595_ = v___x_589_;
v_isShared_596_ = v_isSharedCheck_608_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_diag_593_);
lean_inc(v_postponed_592_);
lean_inc(v_zetaDeltaFVarIds_591_);
lean_inc(v_mctx_590_);
lean_dec(v___x_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_608_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_597_);
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_mctx_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_zetaDeltaFVarIds_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_postponed_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_diag_593_);
v___x_599_ = v_reuseFailAlloc_607_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_600_ = lean_st_ref_put(v___y_568_, v___x_599_);
v___x_601_ = l_Lean_Expr_const___override(v_projName_545_, v___x_549_);
v___x_602_ = l_Lean_mkAppN(v___x_601_, v_params_550_);
v___x_603_ = l_Lean_Expr_app___override(v___x_602_, v_self_551_);
v___x_604_ = l_Lean_Expr_bindingBody_x21(v_b_552_);
v___x_605_ = lean_expr_instantiate1(v___x_604_, v___x_603_);
lean_dec_ref(v___x_603_);
lean_dec_ref(v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
}
}
v___jp_613_:
{
if (lean_obj_tag(v___y_616_) == 0)
{
lean_dec_ref_known(v___y_616_, 1);
v___y_568_ = v___y_614_;
v___y_569_ = v___y_615_;
goto v___jp_567_;
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_617_ = lean_ctor_get(v___y_616_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___y_616_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___y_616_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___y_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
v___jp_625_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = lean_box(0);
lean_inc(v_projName_545_);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v_projName_545_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_634_, 0, v___y_628_);
lean_ctor_set(v___x_634_, 1, v___y_627_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*3, v___x_553_);
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = l_Lean_addDecl(v___x_635_, v___y_631_, v___y_629_, v___y_630_);
lean_dec_ref(v___y_629_);
v___y_614_ = v___y_626_;
v___y_615_ = v___y_630_;
v___y_616_ = v___x_636_;
goto v___jp_613_;
}
v___jp_637_:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v_toCold_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; uint16_t v_optionFlags_649_; uint8_t v_suppressElabErrors_650_; uint8_t v_checkDeprecated_651_; uint8_t v_isRecordingDeps_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_ref_657_; lean_object* v___x_658_; 
v___x_644_ = 0;
lean_inc_ref(v_a_554_);
v___x_645_ = l_Lean_LocalContext_mkForall(v_a_554_, v___x_555_, v___y_639_, v___x_553_, v___x_644_);
lean_dec_ref(v___y_639_);
v_toCold_646_ = lean_ctor_get(v___y_642_, 0);
v_currRecDepth_647_ = lean_ctor_get(v___y_642_, 1);
v_ref_648_ = lean_ctor_get(v___y_642_, 2);
v_optionFlags_649_ = lean_ctor_get_uint16(v___y_642_, sizeof(void*)*3);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*3 + 2);
v_checkDeprecated_651_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*3 + 3);
v_isRecordingDeps_652_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*3 + 4);
v___x_653_ = l_Lean_Expr_inferImplicit(v___x_645_, v___x_546_, v___x_553_);
v___x_654_ = l_Lean_Expr_updateForallBinderInfos(v___x_653_, v_paramInfoOverrides_556_);
lean_inc_ref(v_self_551_);
lean_inc(v_a_547_);
v___x_655_ = l_Lean_Expr_proj___override(v_n_557_, v_a_547_, v_self_551_);
v___x_656_ = l_Lean_LocalContext_mkLambda(v_a_554_, v___x_555_, v___x_655_, v___x_553_, v___x_644_);
lean_dec_ref(v___x_655_);
v_ref_657_ = l_Lean_replaceRef(v_ref_558_, v_ref_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_toCold_646_);
v___x_658_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_658_, 0, v_toCold_646_);
lean_ctor_set(v___x_658_, 1, v_currRecDepth_647_);
lean_ctor_set(v___x_658_, 2, v_ref_657_);
lean_ctor_set_uint16(v___x_658_, sizeof(void*)*3, v_optionFlags_649_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*3 + 2, v_suppressElabErrors_650_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*3 + 3, v_checkDeprecated_651_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*3 + 4, v_isRecordingDeps_652_);
if (v___y_638_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(1);
lean_inc(v_projName_545_);
v___x_660_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_545_, v___x_559_, v___x_654_, v___x_656_, v___x_659_, v___y_643_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_a_661_);
v___x_663_ = l_Lean_addDecl(v___x_662_, v___x_644_, v___x_658_, v___y_643_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
if (v_instImplicit_548_ == 0)
{
lean_object* v___x_664_; 
lean_inc(v_projName_545_);
v___x_664_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_545_, v___y_640_, v___y_641_, v___x_658_, v___y_643_);
lean_dec_ref_known(v___x_658_, 3);
v___y_614_ = v___y_641_;
v___y_615_ = v___y_643_;
v___y_616_ = v___x_664_;
goto v___jp_613_;
}
else
{
lean_dec_ref_known(v___x_658_, 3);
v___y_568_ = v___y_641_;
v___y_569_ = v___y_643_;
goto v___jp_567_;
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref_known(v___x_658_, 3);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_665_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref_known(v___x_658_, 3);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_673_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_660_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_660_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_env_683_; uint8_t v___x_684_; 
lean_inc_ref(v___x_654_);
lean_inc(v_projName_545_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_projName_545_);
lean_ctor_set(v___x_681_, 1, v___x_559_);
lean_ctor_set(v___x_681_, 2, v___x_654_);
v___x_682_ = lean_st_ref_get(v___y_643_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref_n(v_env_683_, 2);
lean_dec(v___x_682_);
v___x_684_ = l_Lean_Environment_hasUnsafe(v_env_683_, v___x_654_);
lean_dec_ref(v___x_654_);
if (v___x_684_ == 0)
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_Environment_hasUnsafe(v_env_683_, v___x_656_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_686_ = lean_box(0);
lean_inc(v_projName_545_);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v_projName_545_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_681_);
lean_ctor_set(v___x_688_, 1, v___x_656_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
v___x_689_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___x_690_ = l_Lean_addDecl(v___x_689_, v___x_644_, v___x_658_, v___y_643_);
lean_dec_ref_known(v___x_658_, 3);
v___y_614_ = v___y_641_;
v___y_615_ = v___y_643_;
v___y_616_ = v___x_690_;
goto v___jp_613_;
}
else
{
v___y_626_ = v___y_641_;
v___y_627_ = v___x_656_;
v___y_628_ = v___x_681_;
v___y_629_ = v___x_658_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_644_;
goto v___jp_625_;
}
}
else
{
lean_dec_ref(v_env_683_);
v___y_626_ = v___y_641_;
v___y_627_ = v___x_656_;
v___y_628_ = v___x_681_;
v___y_629_ = v___x_658_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_644_;
goto v___jp_625_;
}
}
}
v___jp_691_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_Expr_bindingDomain_x21(v_b_552_);
v___x_693_ = lean_expr_consume_type_annotations(v___x_692_);
lean_inc_ref(v___x_693_);
v___x_694_ = l_Lean_Meta_isProp(v___x_693_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_694_) == 0)
{
if (v_a_560_ == 0)
{
lean_object* v_a_695_; uint8_t v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
v___y_638_ = v___x_696_;
v___y_639_ = v___x_693_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
v___y_643_ = v___y_565_;
goto v___jp_637_;
}
else
{
lean_object* v_a_697_; uint8_t v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_694_, 1);
v___x_698_ = lean_unbox(v_a_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_699_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_545_);
v___x_700_ = l_Lean_MessageData_ofName(v_projName_545_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_unbox(v_a_697_);
lean_inc(v_n_557_);
v___x_705_ = l_Lean_MessageData_ofConstName(v_n_557_, v___x_704_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_703_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
lean_inc_ref(v___x_693_);
v___x_709_ = l_Lean_indentExpr(v___x_693_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_558_, v___x_710_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_711_) == 0)
{
uint8_t v___x_712_; 
lean_dec_ref_known(v___x_711_, 1);
v___x_712_ = lean_unbox(v_a_697_);
lean_dec(v_a_697_);
v___y_638_ = v___x_712_;
v___y_639_ = v___x_693_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
v___y_643_ = v___y_565_;
goto v___jp_637_;
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_697_);
lean_dec_ref(v___x_693_);
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_713_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_711_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_unbox(v_a_697_);
lean_dec(v_a_697_);
v___y_638_ = v___x_721_;
v___y_639_ = v___x_693_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
v___y_643_ = v___y_565_;
goto v___jp_637_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v___x_693_);
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_722_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_694_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_694_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_751_ = _args[0];
lean_object* v_projName_752_ = _args[1];
lean_object* v___x_753_ = _args[2];
lean_object* v_a_754_ = _args[3];
lean_object* v_instImplicit_755_ = _args[4];
lean_object* v___x_756_ = _args[5];
lean_object* v_params_757_ = _args[6];
lean_object* v_self_758_ = _args[7];
lean_object* v_b_759_ = _args[8];
lean_object* v___x_760_ = _args[9];
lean_object* v_a_761_ = _args[10];
lean_object* v___x_762_ = _args[11];
lean_object* v_paramInfoOverrides_763_ = _args[12];
lean_object* v_n_764_ = _args[13];
lean_object* v_ref_765_ = _args[14];
lean_object* v___x_766_ = _args[15];
lean_object* v_a_767_ = _args[16];
lean_object* v_____r_768_ = _args[17];
lean_object* v___y_769_ = _args[18];
lean_object* v___y_770_ = _args[19];
lean_object* v___y_771_ = _args[20];
lean_object* v___y_772_ = _args[21];
lean_object* v___y_773_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_774_; uint8_t v___x_17548__boxed_775_; uint8_t v_a_17554__boxed_776_; lean_object* v_res_777_; 
v_instImplicit_boxed_774_ = lean_unbox(v_instImplicit_755_);
v___x_17548__boxed_775_ = lean_unbox(v___x_760_);
v_a_17554__boxed_776_ = lean_unbox(v_a_767_);
v_res_777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_751_, v_projName_752_, v___x_753_, v_a_754_, v_instImplicit_boxed_774_, v___x_756_, v_params_757_, v_self_758_, v_b_759_, v___x_17548__boxed_775_, v_a_761_, v___x_762_, v_paramInfoOverrides_763_, v_n_764_, v_ref_765_, v___x_766_, v_a_17554__boxed_776_, v_____r_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v_ref_765_);
lean_dec(v_paramInfoOverrides_763_);
lean_dec_ref(v___x_762_);
lean_dec_ref(v_b_759_);
lean_dec_ref(v_params_757_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_778_, uint8_t v_isExporting_779_, lean_object* v___x_780_, lean_object* v___y_781_, lean_object* v___x_782_, lean_object* v_a_x3f_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_env_786_; lean_object* v_nextMacroScope_787_; lean_object* v_ngen_788_; lean_object* v_auxDeclNGen_789_; lean_object* v_traceState_790_; lean_object* v_recordedDeps_791_; lean_object* v_messages_792_; lean_object* v_infoState_793_; lean_object* v_snapshotTasks_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_819_; 
v___x_785_ = lean_st_ref_take(v___y_778_);
v_env_786_ = lean_ctor_get(v___x_785_, 0);
v_nextMacroScope_787_ = lean_ctor_get(v___x_785_, 1);
v_ngen_788_ = lean_ctor_get(v___x_785_, 2);
v_auxDeclNGen_789_ = lean_ctor_get(v___x_785_, 3);
v_traceState_790_ = lean_ctor_get(v___x_785_, 4);
v_recordedDeps_791_ = lean_ctor_get(v___x_785_, 6);
v_messages_792_ = lean_ctor_get(v___x_785_, 7);
v_infoState_793_ = lean_ctor_get(v___x_785_, 8);
v_snapshotTasks_794_ = lean_ctor_get(v___x_785_, 9);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_785_, 5);
lean_dec(v_unused_820_);
v___x_796_ = v___x_785_;
v_isShared_797_ = v_isSharedCheck_819_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snapshotTasks_794_);
lean_inc(v_infoState_793_);
lean_inc(v_messages_792_);
lean_inc(v_recordedDeps_791_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_789_);
lean_inc(v_ngen_788_);
lean_inc(v_nextMacroScope_787_);
lean_inc(v_env_786_);
lean_dec(v___x_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_819_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_Environment_setExporting(v_env_786_, v_isExporting_779_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 5, v___x_780_);
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_nextMacroScope_787_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_ngen_788_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_auxDeclNGen_789_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_traceState_790_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_recordedDeps_791_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_messages_792_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_infoState_793_);
lean_ctor_set(v_reuseFailAlloc_818_, 9, v_snapshotTasks_794_);
v___x_800_ = v_reuseFailAlloc_818_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_mctx_803_; lean_object* v_zetaDeltaFVarIds_804_; lean_object* v_postponed_805_; lean_object* v_diag_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_816_; 
v___x_801_ = lean_st_ref_put(v___y_778_, v___x_800_);
v___x_802_ = lean_st_ref_take(v___y_781_);
v_mctx_803_ = lean_ctor_get(v___x_802_, 0);
v_zetaDeltaFVarIds_804_ = lean_ctor_get(v___x_802_, 2);
v_postponed_805_ = lean_ctor_get(v___x_802_, 3);
v_diag_806_ = lean_ctor_get(v___x_802_, 4);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_802_, 1);
lean_dec(v_unused_817_);
v___x_808_ = v___x_802_;
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_diag_806_);
lean_inc(v_postponed_805_);
lean_inc(v_zetaDeltaFVarIds_804_);
lean_inc(v_mctx_803_);
lean_dec(v___x_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_816_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_box(0);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_782_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_mctx_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_zetaDeltaFVarIds_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_postponed_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_diag_806_);
v___x_812_ = v_reuseFailAlloc_815_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_st_ref_put(v___y_781_, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_810_);
return v___x_814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_821_, lean_object* v_isExporting_822_, lean_object* v___x_823_, lean_object* v___y_824_, lean_object* v___x_825_, lean_object* v_a_x3f_826_, lean_object* v___y_827_){
_start:
{
uint8_t v_isExporting_boxed_828_; lean_object* v_res_829_; 
v_isExporting_boxed_828_ = lean_unbox(v_isExporting_822_);
v_res_829_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_821_, v_isExporting_boxed_828_, v___x_823_, v___y_824_, v___x_825_, v_a_x3f_826_);
lean_dec(v_a_x3f_826_);
lean_dec(v___y_824_);
lean_dec(v___y_821_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_830_, uint8_t v_isExporting_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; lean_object* v___x_839_; uint8_t v_isModule_840_; 
v___x_837_ = lean_st_ref_get(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = l_Lean_Environment_header(v_env_838_);
v_isModule_840_ = lean_ctor_get_uint8(v___x_839_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_839_);
if (v_isModule_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref(v_env_838_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v___x_841_ = lean_apply_5(v_x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_841_;
}
else
{
uint8_t v_isExporting_842_; 
v_isExporting_842_ = lean_ctor_get_uint8(v_env_838_, sizeof(void*)*13);
lean_dec_ref(v_env_838_);
if (v_isExporting_831_ == 0)
{
if (v_isExporting_842_ == 0)
{
lean_object* v___x_909_; 
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v___x_909_ = lean_apply_5(v_x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_909_;
}
else
{
goto v___jp_843_;
}
}
else
{
if (v_isExporting_842_ == 0)
{
goto v___jp_843_;
}
else
{
lean_object* v___x_910_; 
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v___x_910_ = lean_apply_5(v_x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
return v___x_910_;
}
}
v___jp_843_:
{
lean_object* v___x_844_; lean_object* v_env_845_; lean_object* v_nextMacroScope_846_; lean_object* v_ngen_847_; lean_object* v_auxDeclNGen_848_; lean_object* v_traceState_849_; lean_object* v_recordedDeps_850_; lean_object* v_messages_851_; lean_object* v_infoState_852_; lean_object* v_snapshotTasks_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_907_; 
v___x_844_ = lean_st_ref_take(v___y_835_);
v_env_845_ = lean_ctor_get(v___x_844_, 0);
v_nextMacroScope_846_ = lean_ctor_get(v___x_844_, 1);
v_ngen_847_ = lean_ctor_get(v___x_844_, 2);
v_auxDeclNGen_848_ = lean_ctor_get(v___x_844_, 3);
v_traceState_849_ = lean_ctor_get(v___x_844_, 4);
v_recordedDeps_850_ = lean_ctor_get(v___x_844_, 6);
v_messages_851_ = lean_ctor_get(v___x_844_, 7);
v_infoState_852_ = lean_ctor_get(v___x_844_, 8);
v_snapshotTasks_853_ = lean_ctor_get(v___x_844_, 9);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_844_, 5);
lean_dec(v_unused_908_);
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_907_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snapshotTasks_853_);
lean_inc(v_infoState_852_);
lean_inc(v_messages_851_);
lean_inc(v_recordedDeps_850_);
lean_inc(v_traceState_849_);
lean_inc(v_auxDeclNGen_848_);
lean_inc(v_ngen_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_env_845_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_907_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = l_Lean_Environment_setExporting(v_env_845_, v_isExporting_831_);
v___x_858_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 5, v___x_858_);
lean_ctor_set(v___x_855_, 0, v___x_857_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_ngen_847_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_auxDeclNGen_848_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_traceState_849_);
lean_ctor_set(v_reuseFailAlloc_906_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_906_, 6, v_recordedDeps_850_);
lean_ctor_set(v_reuseFailAlloc_906_, 7, v_messages_851_);
lean_ctor_set(v_reuseFailAlloc_906_, 8, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_906_, 9, v_snapshotTasks_853_);
v___x_860_ = v_reuseFailAlloc_906_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v_zetaDeltaFVarIds_864_; lean_object* v_postponed_865_; lean_object* v_diag_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_904_; 
v___x_861_ = lean_st_ref_put(v___y_835_, v___x_860_);
v___x_862_ = lean_st_ref_take(v___y_833_);
v_mctx_863_ = lean_ctor_get(v___x_862_, 0);
v_zetaDeltaFVarIds_864_ = lean_ctor_get(v___x_862_, 2);
v_postponed_865_ = lean_ctor_get(v___x_862_, 3);
v_diag_866_ = lean_ctor_get(v___x_862_, 4);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_862_, 1);
lean_dec(v_unused_905_);
v___x_868_ = v___x_862_;
v_isShared_869_ = v_isSharedCheck_904_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_diag_866_);
lean_inc(v_postponed_865_);
lean_inc(v_zetaDeltaFVarIds_864_);
lean_inc(v_mctx_863_);
lean_dec(v___x_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_904_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_mctx_863_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_zetaDeltaFVarIds_864_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_postponed_865_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_diag_866_);
v___x_872_ = v_reuseFailAlloc_903_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v_r_874_; 
v___x_873_ = lean_st_ref_put(v___y_833_, v___x_872_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
v_r_874_ = lean_apply_5(v_x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
if (lean_obj_tag(v_r_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_891_; 
v_a_875_ = lean_ctor_get(v_r_874_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_r_874_);
if (v_isSharedCheck_891_ == 0)
{
v___x_877_ = v_r_874_;
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v_r_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
lean_inc(v_a_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 1);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_890_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v___x_881_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_835_, v_isExporting_842_, v___x_858_, v___y_833_, v___x_870_, v___x_880_);
lean_dec_ref(v___x_880_);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v___x_881_, 0);
lean_dec(v_unused_889_);
v___x_883_ = v___x_881_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_881_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v_a_875_);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_875_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_a_892_ = lean_ctor_get(v_r_874_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v_r_874_, 1);
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_835_, v_isExporting_842_, v___x_858_, v___y_833_, v___x_870_, v___x_893_);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_894_, 0);
lean_dec(v_unused_902_);
v___x_896_ = v___x_894_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_dec(v___x_894_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set_tag(v___x_896_, 1);
lean_ctor_set(v___x_896_, 0, v_a_892_);
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_892_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_911_, lean_object* v_isExporting_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v_isExporting_boxed_918_; lean_object* v_res_919_; 
v_isExporting_boxed_918_ = lean_unbox(v_isExporting_912_);
v_res_919_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_911_, v_isExporting_boxed_918_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_920_, uint8_t v_when_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (v_when_921_ == 0)
{
lean_object* v___x_927_; 
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
v___x_927_ = lean_apply_5(v_x_920_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
return v___x_927_;
}
else
{
uint8_t v___x_928_; lean_object* v___x_929_; 
v___x_928_ = 0;
v___x_929_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_920_, v___x_928_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_930_, lean_object* v_when_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v_when_boxed_937_; lean_object* v_res_938_; 
v_when_boxed_937_ = lean_unbox(v_when_931_);
v_res_938_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_930_, v_when_boxed_937_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_939_, lean_object* v_projDecls_940_, lean_object* v___x_941_, lean_object* v___x_942_, uint8_t v_instImplicit_943_, lean_object* v___x_944_, lean_object* v_params_945_, lean_object* v_self_946_, lean_object* v_a_947_, lean_object* v___x_948_, lean_object* v_n_949_, lean_object* v___x_950_, uint8_t v_a_951_, lean_object* v_a_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v___x_959_; 
v___x_959_ = lean_nat_dec_lt(v_a_952_, v_upperBound_939_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v_a_952_);
lean_dec(v___x_950_);
lean_dec(v_n_949_);
lean_dec_ref(v___x_948_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_self_946_);
lean_dec_ref(v_params_945_);
lean_dec(v___x_944_);
lean_dec(v___x_942_);
lean_dec_ref(v___x_941_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_953_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; lean_object* v_ref_962_; lean_object* v_projName_963_; lean_object* v_paramInfoOverrides_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___f_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___y_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_961_ = lean_array_fget_borrowed(v_projDecls_940_, v_a_952_);
v_ref_962_ = lean_ctor_get(v___x_961_, 0);
v_projName_963_ = lean_ctor_get(v___x_961_, 1);
v_paramInfoOverrides_964_ = lean_ctor_get(v___x_961_, 2);
v___x_965_ = lean_box(v_instImplicit_943_);
v___x_966_ = lean_box(v___x_959_);
v___x_967_ = lean_box(v_a_951_);
lean_inc(v___x_950_);
lean_inc_n(v_ref_962_, 2);
lean_inc_n(v_n_949_, 2);
lean_inc(v_paramInfoOverrides_964_);
lean_inc_ref(v___x_948_);
lean_inc_ref(v_a_947_);
lean_inc_ref(v_b_953_);
lean_inc_ref(v_self_946_);
lean_inc_ref(v_params_945_);
lean_inc(v___x_944_);
lean_inc(v_a_952_);
lean_inc(v___x_942_);
lean_inc_n(v_projName_963_, 2);
lean_inc_ref(v___x_941_);
v___f_968_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_968_, 0, v___x_941_);
lean_closure_set(v___f_968_, 1, v_projName_963_);
lean_closure_set(v___f_968_, 2, v___x_942_);
lean_closure_set(v___f_968_, 3, v_a_952_);
lean_closure_set(v___f_968_, 4, v___x_965_);
lean_closure_set(v___f_968_, 5, v___x_944_);
lean_closure_set(v___f_968_, 6, v_params_945_);
lean_closure_set(v___f_968_, 7, v_self_946_);
lean_closure_set(v___f_968_, 8, v_b_953_);
lean_closure_set(v___f_968_, 9, v___x_966_);
lean_closure_set(v___f_968_, 10, v_a_947_);
lean_closure_set(v___f_968_, 11, v___x_948_);
lean_closure_set(v___f_968_, 12, v_paramInfoOverrides_964_);
lean_closure_set(v___f_968_, 13, v_n_949_);
lean_closure_set(v___f_968_, 14, v_ref_962_);
lean_closure_set(v___f_968_, 15, v___x_950_);
lean_closure_set(v___f_968_, 16, v___x_967_);
v___x_969_ = l_Lean_Expr_isForall(v_b_953_);
lean_dec_ref(v_b_953_);
v___x_970_ = lean_box(v___x_969_);
v___y_971_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_971_, 0, v___x_970_);
lean_closure_set(v___y_971_, 1, v_projName_963_);
lean_closure_set(v___y_971_, 2, v_n_949_);
lean_closure_set(v___y_971_, 3, v_ref_962_);
lean_closure_set(v___y_971_, 4, v___f_968_);
v___x_972_ = l_Lean_isPrivateName(v_projName_963_);
v___x_973_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_971_, v___x_972_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_add(v_a_952_, v___x_975_);
lean_dec(v_a_952_);
v_a_952_ = v___x_976_;
v_b_953_ = v_a_974_;
goto _start;
}
else
{
lean_dec(v_a_952_);
lean_dec(v___x_950_);
lean_dec(v_n_949_);
lean_dec_ref(v___x_948_);
lean_dec_ref(v_a_947_);
lean_dec_ref(v_self_946_);
lean_dec_ref(v_params_945_);
lean_dec(v___x_944_);
lean_dec(v___x_942_);
lean_dec_ref(v___x_941_);
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_978_ = _args[0];
lean_object* v_projDecls_979_ = _args[1];
lean_object* v___x_980_ = _args[2];
lean_object* v___x_981_ = _args[3];
lean_object* v_instImplicit_982_ = _args[4];
lean_object* v___x_983_ = _args[5];
lean_object* v_params_984_ = _args[6];
lean_object* v_self_985_ = _args[7];
lean_object* v_a_986_ = _args[8];
lean_object* v___x_987_ = _args[9];
lean_object* v_n_988_ = _args[10];
lean_object* v___x_989_ = _args[11];
lean_object* v_a_990_ = _args[12];
lean_object* v_a_991_ = _args[13];
lean_object* v_b_992_ = _args[14];
lean_object* v___y_993_ = _args[15];
lean_object* v___y_994_ = _args[16];
lean_object* v___y_995_ = _args[17];
lean_object* v___y_996_ = _args[18];
lean_object* v___y_997_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_998_; uint8_t v_a_18167__boxed_999_; lean_object* v_res_1000_; 
v_instImplicit_boxed_998_ = lean_unbox(v_instImplicit_982_);
v_a_18167__boxed_999_ = lean_unbox(v_a_990_);
v_res_1000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_978_, v_projDecls_979_, v___x_980_, v___x_981_, v_instImplicit_boxed_998_, v___x_983_, v_params_984_, v_self_985_, v_a_986_, v___x_987_, v_n_988_, v___x_989_, v_a_18167__boxed_999_, v_a_991_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec_ref(v_projDecls_979_);
lean_dec(v_upperBound_978_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1001_, lean_object* v_as_1002_, size_t v_sz_1003_, size_t v_i_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_a_1011_; uint8_t v___x_1015_; 
v___x_1015_ = lean_usize_dec_lt(v_i_1004_, v_sz_1003_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_b_1005_);
return v___x_1016_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_a_1017_ = lean_array_uget_borrowed(v_as_1002_, v_i_1004_);
v___x_1018_ = l_Lean_Expr_fvarId_x21(v_a_1017_);
lean_inc(v___x_1018_);
v___x_1019_ = l_Lean_FVarId_getDecl___redArg(v___x_1018_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; uint8_t v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = l_Lean_LocalDecl_binderInfo(v_a_1020_);
v___x_1022_ = l_Lean_BinderInfo_isInstImplicit(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = l_Lean_LocalDecl_type(v_a_1020_);
lean_dec(v_a_1020_);
v___x_1027_ = l_Lean_Expr_isOutParam(v___x_1026_);
lean_dec_ref(v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = 0;
v___x_1029_ = l_Lean_LocalContext_setBinderInfo(v_b_1005_, v___x_1018_, v___x_1028_);
v_a_1011_ = v___x_1029_;
goto v___jp_1010_;
}
else
{
goto v___jp_1023_;
}
}
else
{
lean_dec(v_a_1020_);
goto v___jp_1023_;
}
v___jp_1023_:
{
if (v___x_1022_ == 0)
{
lean_dec(v___x_1018_);
v_a_1011_ = v_b_1005_;
goto v___jp_1010_;
}
else
{
if (v_instImplicit_1001_ == 0)
{
lean_dec(v___x_1018_);
v_a_1011_ = v_b_1005_;
goto v___jp_1010_;
}
else
{
uint8_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = 1;
v___x_1025_ = l_Lean_LocalContext_setBinderInfo(v_b_1005_, v___x_1018_, v___x_1024_);
v_a_1011_ = v___x_1025_;
goto v___jp_1010_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_b_1005_);
v_a_1030_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1019_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1019_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
v___jp_1010_:
{
size_t v___x_1012_; size_t v___x_1013_; 
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_add(v_i_1004_, v___x_1012_);
v_i_1004_ = v___x_1013_;
v_b_1005_ = v_a_1011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1038_, lean_object* v_as_1039_, lean_object* v_sz_1040_, lean_object* v_i_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_instImplicit_boxed_1047_; size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_instImplicit_boxed_1047_ = lean_unbox(v_instImplicit_1038_);
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1040_);
lean_dec(v_sz_1040_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1041_);
lean_dec(v_i_1041_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1047_, v_as_1039_, v_sz_boxed_1048_, v_i_boxed_1049_, v_b_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v_as_1039_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1051_, uint8_t v_instImplicit_1052_, lean_object* v_projDecls_1053_, lean_object* v_toConstantVal_1054_, lean_object* v_numParams_1055_, lean_object* v___x_1056_, lean_object* v_n_1057_, lean_object* v_levelParams_1058_, uint8_t v_a_1059_, lean_object* v_ctorType_1060_, lean_object* v_self_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_lctx_1067_; lean_object* v___x_1068_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v_lctx_1067_ = lean_ctor_get(v___y_1062_, 2);
lean_inc_ref(v_self_1061_);
lean_inc_ref(v_params_1051_);
v___x_1068_ = lean_array_push(v_params_1051_, v_self_1061_);
v_sz_1069_ = lean_array_size(v_params_1051_);
v___x_1070_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1067_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1052_, v_params_1051_, v_sz_1069_, v___x_1070_, v_lctx_1067_, v___y_1062_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_array_get_size(v_projDecls_1053_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1073_, v_projDecls_1053_, v_toConstantVal_1054_, v_numParams_1055_, v_instImplicit_1052_, v___x_1056_, v_params_1051_, v_self_1061_, v_a_1072_, v___x_1068_, v_n_1057_, v_levelParams_1058_, v_a_1059_, v___x_1074_, v_ctorType_1060_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v___x_1075_, 0);
lean_dec(v_unused_1084_);
v___x_1077_ = v___x_1075_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___x_1075_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1075_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1075_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_self_1061_);
lean_dec_ref(v_ctorType_1060_);
lean_dec(v_levelParams_1058_);
lean_dec(v_n_1057_);
lean_dec(v___x_1056_);
lean_dec(v_numParams_1055_);
lean_dec_ref(v_toConstantVal_1054_);
lean_dec_ref(v_params_1051_);
v_a_1093_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1071_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1071_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1101_, lean_object* v_instImplicit_1102_, lean_object* v_projDecls_1103_, lean_object* v_toConstantVal_1104_, lean_object* v_numParams_1105_, lean_object* v___x_1106_, lean_object* v_n_1107_, lean_object* v_levelParams_1108_, lean_object* v_a_1109_, lean_object* v_ctorType_1110_, lean_object* v_self_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v_instImplicit_boxed_1117_; uint8_t v_a_18305__boxed_1118_; lean_object* v_res_1119_; 
v_instImplicit_boxed_1117_ = lean_unbox(v_instImplicit_1102_);
v_a_18305__boxed_1118_ = lean_unbox(v_a_1109_);
v_res_1119_ = l_Lean_Meta_mkProjections___lam__0(v_params_1101_, v_instImplicit_boxed_1117_, v_projDecls_1103_, v_toConstantVal_1104_, v_numParams_1105_, v___x_1106_, v_n_1107_, v_levelParams_1108_, v_a_18305__boxed_1118_, v_ctorType_1110_, v_self_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_projDecls_1103_);
return v_res_1119_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1128_ = l_Lean_stringToMessageData(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1129_, lean_object* v_projDecls_1130_, lean_object* v_toConstantVal_1131_, lean_object* v_numParams_1132_, lean_object* v___x_1133_, lean_object* v_n_1134_, lean_object* v_levelParams_1135_, uint8_t v_a_1136_, lean_object* v_params_1137_, lean_object* v_ctorType_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___f_1157_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1155_ = lean_box(v_instImplicit_1129_);
v___x_1156_ = lean_box(v_a_1136_);
lean_inc(v_n_1134_);
lean_inc(v___x_1133_);
lean_inc(v_numParams_1132_);
lean_inc_ref(v_params_1137_);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1157_, 0, v_params_1137_);
lean_closure_set(v___f_1157_, 1, v___x_1155_);
lean_closure_set(v___f_1157_, 2, v_projDecls_1130_);
lean_closure_set(v___f_1157_, 3, v_toConstantVal_1131_);
lean_closure_set(v___f_1157_, 4, v_numParams_1132_);
lean_closure_set(v___f_1157_, 5, v___x_1133_);
lean_closure_set(v___f_1157_, 6, v_n_1134_);
lean_closure_set(v___f_1157_, 7, v_levelParams_1135_);
lean_closure_set(v___f_1157_, 8, v___x_1156_);
lean_closure_set(v___f_1157_, 9, v_ctorType_1138_);
v___x_1163_ = lean_array_get_size(v_params_1137_);
v___x_1164_ = lean_nat_dec_eq(v___x_1163_, v_numParams_1132_);
lean_dec(v_numParams_1132_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec_ref(v___f_1157_);
lean_dec_ref(v_params_1137_);
lean_dec(v___x_1133_);
v___x_1165_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1166_ = l_Lean_MessageData_ofConstName(v_n_1134_, v___x_1164_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1169_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1170_;
}
else
{
goto v___jp_1158_;
}
v___jp_1144_:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1153_ = 0;
v___x_1154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1152_, v___y_1151_, v___y_1150_, v___y_1146_, v___x_1153_, v___y_1145_, v___y_1149_, v___y_1147_, v___y_1148_);
return v___x_1154_;
}
v___jp_1158_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = l_Lean_Expr_const___override(v_n_1134_, v___x_1133_);
v___x_1160_ = l_Lean_mkAppN(v___x_1159_, v_params_1137_);
lean_dec_ref(v_params_1137_);
if (v_instImplicit_1129_ == 0)
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
v___y_1145_ = v___y_1139_;
v___y_1146_ = v___f_1157_;
v___y_1147_ = v___y_1141_;
v___y_1148_ = v___y_1142_;
v___y_1149_ = v___y_1140_;
v___y_1150_ = v___x_1160_;
v___y_1151_ = v___x_1161_;
goto v___jp_1144_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = 3;
v___y_1145_ = v___y_1139_;
v___y_1146_ = v___f_1157_;
v___y_1147_ = v___y_1141_;
v___y_1148_ = v___y_1142_;
v___y_1149_ = v___y_1140_;
v___y_1150_ = v___x_1160_;
v___y_1151_ = v___x_1162_;
goto v___jp_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1171_, lean_object* v_projDecls_1172_, lean_object* v_toConstantVal_1173_, lean_object* v_numParams_1174_, lean_object* v___x_1175_, lean_object* v_n_1176_, lean_object* v_levelParams_1177_, lean_object* v_a_1178_, lean_object* v_params_1179_, lean_object* v_ctorType_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_instImplicit_boxed_1186_; uint8_t v_a_18409__boxed_1187_; lean_object* v_res_1188_; 
v_instImplicit_boxed_1186_ = lean_unbox(v_instImplicit_1171_);
v_a_18409__boxed_1187_ = lean_unbox(v_a_1178_);
v_res_1188_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1186_, v_projDecls_1172_, v_toConstantVal_1173_, v_numParams_1174_, v___x_1175_, v_n_1176_, v_levelParams_1177_, v_a_18409__boxed_1187_, v_params_1179_, v_ctorType_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
if (lean_obj_tag(v_a_1189_) == 0)
{
lean_object* v___x_1191_; 
v___x_1191_ = l_List_reverse___redArg(v_a_1190_);
return v___x_1191_;
}
else
{
lean_object* v_head_1192_; lean_object* v_tail_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v_head_1192_ = lean_ctor_get(v_a_1189_, 0);
v_tail_1193_ = lean_ctor_get(v_a_1189_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1189_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v_a_1189_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_tail_1193_);
lean_inc(v_head_1192_);
lean_dec(v_a_1189_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = l_Lean_mkLevelParam(v_head_1192_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_a_1190_);
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_a_1190_);
v___x_1199_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v_a_1189_ = v_tail_1193_;
v_a_1190_ = v___x_1199_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_instMonadEIO___redArg();
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_toApplicative_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1277_; 
v___x_1214_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1215_ = l_StateRefT_x27_instMonad___redArg(v___x_1214_);
v_toApplicative_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1215_, 1);
lean_dec(v_unused_1278_);
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1277_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_toApplicative_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1277_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_toFunctor_1220_; lean_object* v_toSeq_1221_; lean_object* v_toSeqLeft_1222_; lean_object* v_toSeqRight_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1275_; 
v_toFunctor_1220_ = lean_ctor_get(v_toApplicative_1216_, 0);
v_toSeq_1221_ = lean_ctor_get(v_toApplicative_1216_, 2);
v_toSeqLeft_1222_ = lean_ctor_get(v_toApplicative_1216_, 3);
v_toSeqRight_1223_ = lean_ctor_get(v_toApplicative_1216_, 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_toApplicative_1216_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_toApplicative_1216_, 1);
lean_dec(v_unused_1276_);
v___x_1225_ = v_toApplicative_1216_;
v_isShared_1226_ = v_isSharedCheck_1275_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_toSeqRight_1223_);
lean_inc(v_toSeqLeft_1222_);
lean_inc(v_toSeq_1221_);
lean_inc(v_toFunctor_1220_);
lean_dec(v_toApplicative_1216_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1275_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___x_1236_; 
v___f_1227_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1228_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1220_);
v___f_1229_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1229_, 0, v_toFunctor_1220_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toFunctor_1220_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___f_1229_);
lean_ctor_set(v___x_1231_, 1, v___f_1230_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toSeqRight_1223_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toSeqLeft_1222_);
v___f_1234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1234_, 0, v_toSeq_1221_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 4, v___f_1232_);
lean_ctor_set(v___x_1225_, 3, v___f_1233_);
lean_ctor_set(v___x_1225_, 2, v___f_1234_);
lean_ctor_set(v___x_1225_, 1, v___f_1227_);
lean_ctor_set(v___x_1225_, 0, v___x_1231_);
v___x_1236_ = v___x_1225_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___f_1227_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v___f_1234_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___f_1233_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v___f_1232_);
v___x_1236_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1238_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___f_1228_);
lean_ctor_set(v___x_1218_, 0, v___x_1236_);
v___x_1238_ = v___x_1218_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v___f_1228_);
v___x_1238_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v_toApplicative_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1271_; 
v___x_1239_ = l_StateRefT_x27_instMonad___redArg(v___x_1238_);
v_toApplicative_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1239_, 1);
lean_dec(v_unused_1272_);
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_toApplicative_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_toFunctor_1244_; lean_object* v_toSeq_1245_; lean_object* v_toSeqLeft_1246_; lean_object* v_toSeqRight_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1269_; 
v_toFunctor_1244_ = lean_ctor_get(v_toApplicative_1240_, 0);
v_toSeq_1245_ = lean_ctor_get(v_toApplicative_1240_, 2);
v_toSeqLeft_1246_ = lean_ctor_get(v_toApplicative_1240_, 3);
v_toSeqRight_1247_ = lean_ctor_get(v_toApplicative_1240_, 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v_toApplicative_1240_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v_toApplicative_1240_, 1);
lean_dec(v_unused_1270_);
v___x_1249_ = v_toApplicative_1240_;
v_isShared_1250_ = v_isSharedCheck_1269_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_toSeqRight_1247_);
lean_inc(v_toSeqLeft_1246_);
lean_inc(v_toSeq_1245_);
lean_inc(v_toFunctor_1244_);
lean_dec(v_toApplicative_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1269_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; lean_object* v___x_1260_; 
v___f_1251_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1252_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1244_);
v___f_1253_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1253_, 0, v_toFunctor_1244_);
v___f_1254_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1254_, 0, v_toFunctor_1244_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___f_1253_);
lean_ctor_set(v___x_1255_, 1, v___f_1254_);
v___f_1256_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1256_, 0, v_toSeqRight_1247_);
v___f_1257_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1257_, 0, v_toSeqLeft_1246_);
v___f_1258_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1258_, 0, v_toSeq_1245_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 4, v___f_1256_);
lean_ctor_set(v___x_1249_, 3, v___f_1257_);
lean_ctor_set(v___x_1249_, 2, v___f_1258_);
lean_ctor_set(v___x_1249_, 1, v___f_1251_);
lean_ctor_set(v___x_1249_, 0, v___x_1255_);
v___x_1260_ = v___x_1249_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___f_1251_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v___f_1258_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v___f_1257_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v___f_1256_);
v___x_1260_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___f_1252_);
lean_ctor_set(v___x_1242_, 0, v___x_1260_);
v___x_1262_ = v___x_1242_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___f_1252_);
v___x_1262_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_13260__overap_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = l_instInhabitedOfMonad___redArg(v___x_1262_, v___x_1263_);
v___x_13260__overap_1265_ = lean_panic_fn_borrowed(v___x_1264_, v_msg_1208_);
lean_dec(v___x_1264_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
v___x_1266_ = lean_apply_5(v___x_13260__overap_1265_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, lean_box(0));
return v___x_1266_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1292_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1293_ = lean_unsigned_to_nat(11u);
v___x_1294_ = lean_unsigned_to_nat(122u);
v___x_1295_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1296_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1297_ = l_mkPanicMessageWithDecl(v___x_1296_, v___x_1295_, v___x_1294_, v___x_1293_, v___x_1292_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_st_ref_get(v___y_1302_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = 0;
lean_inc(v_constName_1298_);
v___x_1315_ = l_Lean_Environment_findAsync_x3f(v_env_1313_, v_constName_1298_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 1)
{
lean_object* v_val_1316_; uint8_t v_kind_1317_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v_kind_1317_ = lean_ctor_get_uint8(v_val_1316_, sizeof(void*)*3);
if (v_kind_1317_ == 6)
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1316_);
if (lean_obj_tag(v___x_1318_) == 6)
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_constName_1298_);
v_val_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_val_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec_ref(v___x_1318_);
v___x_1327_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1328_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1327_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
if (lean_obj_tag(v_a_1329_) == 0)
{
lean_del_object(v___x_1331_);
goto v___jp_1304_;
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1335_; 
lean_dec(v_constName_1298_);
v_val_1333_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_a_1329_, 1);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v_val_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_val_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_constName_1298_);
v_a_1338_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1328_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1328_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
else
{
lean_dec(v_val_1316_);
goto v___jp_1304_;
}
}
else
{
lean_dec(v___x_1315_);
goto v___jp_1304_;
}
v___jp_1304_:
{
lean_object* v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1305_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1306_ = 0;
v___x_1307_ = l_Lean_MessageData_ofConstName(v_constName_1298_, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1305_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1310_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1352_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v_env_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_st_ref_get(v___y_1360_);
v_env_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc_ref(v_env_1363_);
lean_dec(v___x_1362_);
lean_inc(v_constName_1356_);
v___x_1364_ = l_Lean_isInductiveCore_x3f(v_env_1363_, v_constName_1356_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1365_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1366_ = 0;
v___x_1367_ = l_Lean_MessageData_ofConstName(v_constName_1356_, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1370_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_constName_1356_);
v_val_1372_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1364_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_val_1372_);
lean_dec(v___x_1364_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 0);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1392_ = l_Lean_stringToMessageData(v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1393_, lean_object* v___x_1394_, uint8_t v_instImplicit_1395_, lean_object* v_projDecls_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
lean_inc(v_n_1393_);
v___x_1402_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1393_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1444_ = l_Lean_InductiveVal_numCtors(v_a_1403_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_a_1403_);
lean_dec_ref(v_projDecls_1396_);
v___x_1447_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1448_ = l_Lean_MessageData_ofConstName(v_n_1393_, v___x_1446_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1451_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1452_;
}
else
{
v___y_1405_ = v___y_1397_;
v___y_1406_ = v___y_1398_;
v___y_1407_ = v___y_1399_;
v___y_1408_ = v___y_1400_;
goto v___jp_1404_;
}
v___jp_1404_:
{
lean_object* v_toConstantVal_1409_; lean_object* v_numParams_1410_; lean_object* v_ctors_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_toConstantVal_1409_ = lean_ctor_get(v_a_1403_, 0);
lean_inc_ref(v_toConstantVal_1409_);
v_numParams_1410_ = lean_ctor_get(v_a_1403_, 1);
lean_inc(v_numParams_1410_);
v_ctors_1411_ = lean_ctor_get(v_a_1403_, 4);
lean_inc(v_ctors_1411_);
lean_dec(v_a_1403_);
v___x_1412_ = l_List_head_x21___redArg(v___x_1394_, v_ctors_1411_);
lean_dec(v_ctors_1411_);
v___x_1413_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1412_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_levelParams_1415_; lean_object* v_type_1416_; lean_object* v___x_1417_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v_levelParams_1415_ = lean_ctor_get(v_toConstantVal_1409_, 1);
lean_inc(v_levelParams_1415_);
v_type_1416_ = lean_ctor_get(v_toConstantVal_1409_, 2);
lean_inc_ref(v_type_1416_);
lean_dec_ref(v_toConstantVal_1409_);
v___x_1417_ = l_Lean_Meta_isPropFormerType(v_type_1416_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_toConstantVal_1418_; lean_object* v_a_1419_; lean_object* v_type_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v_toConstantVal_1418_ = lean_ctor_get(v_a_1414_, 0);
lean_inc_ref(v_toConstantVal_1418_);
lean_dec(v_a_1414_);
v_a_1419_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1417_, 1);
v_type_1420_ = lean_ctor_get(v_toConstantVal_1418_, 2);
lean_inc_ref(v_type_1420_);
v___x_1421_ = lean_box(0);
lean_inc(v_levelParams_1415_);
v___x_1422_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1415_, v___x_1421_);
v___x_1423_ = lean_box(v_instImplicit_1395_);
lean_inc(v_numParams_1410_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1424_, 0, v___x_1423_);
lean_closure_set(v___f_1424_, 1, v_projDecls_1396_);
lean_closure_set(v___f_1424_, 2, v_toConstantVal_1418_);
lean_closure_set(v___f_1424_, 3, v_numParams_1410_);
lean_closure_set(v___f_1424_, 4, v___x_1422_);
lean_closure_set(v___f_1424_, 5, v_n_1393_);
lean_closure_set(v___f_1424_, 6, v_levelParams_1415_);
lean_closure_set(v___f_1424_, 7, v_a_1419_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_numParams_1410_);
v___x_1426_ = 0;
v___x_1427_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1420_, v___x_1425_, v___f_1424_, v___x_1426_, v___x_1426_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_levelParams_1415_);
lean_dec(v_a_1414_);
lean_dec(v_numParams_1410_);
lean_dec_ref(v_projDecls_1396_);
lean_dec(v_n_1393_);
v_a_1428_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1417_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1417_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_numParams_1410_);
lean_dec_ref(v_toConstantVal_1409_);
lean_dec_ref(v_projDecls_1396_);
lean_dec(v_n_1393_);
v_a_1436_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1413_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1413_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_projDecls_1396_);
lean_dec(v_n_1393_);
v_a_1453_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1402_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1402_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1461_, lean_object* v___x_1462_, lean_object* v_instImplicit_1463_, lean_object* v_projDecls_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_instImplicit_boxed_1470_; lean_object* v_res_1471_; 
v_instImplicit_boxed_1470_ = lean_unbox(v_instImplicit_1463_);
v_res_1471_ = l_Lean_Meta_mkProjections___lam__2(v_n_1461_, v___x_1462_, v_instImplicit_boxed_1470_, v_projDecls_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___x_1462_);
return v_res_1471_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(32u);
v___x_1475_ = lean_mk_empty_array_with_capacity(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1477_ = ((size_t)5ULL);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_unsigned_to_nat(32u);
v___x_1480_ = lean_mk_empty_array_with_capacity(v___x_1479_);
v___x_1481_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1478_);
lean_ctor_set(v___x_1482_, 3, v___x_1478_);
lean_ctor_set_usize(v___x_1482_, 4, v___x_1477_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = lean_box(1);
v___x_1484_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1485_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1484_);
lean_ctor_set(v___x_1486_, 2, v___x_1483_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1489_, lean_object* v_projDecls_1490_, uint8_t v_instImplicit_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_box(v_instImplicit_1491_);
v___f_1499_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1499_, 0, v_n_1489_);
lean_closure_set(v___f_1499_, 1, v___x_1497_);
lean_closure_set(v___f_1499_, 2, v___x_1498_);
lean_closure_set(v___f_1499_, 3, v_projDecls_1490_);
v___x_1500_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1501_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1502_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1500_, v___x_1501_, v___f_1499_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1503_, lean_object* v_projDecls_1504_, lean_object* v_instImplicit_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
uint8_t v_instImplicit_boxed_1511_; lean_object* v_res_1512_; 
v_instImplicit_boxed_1511_ = lean_unbox(v_instImplicit_1505_);
v_res_1512_ = l_Lean_Meta_mkProjections(v_n_1503_, v_projDecls_1504_, v_instImplicit_boxed_1511_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1513_, lean_object* v_as_1514_, size_t v_sz_1515_, size_t v_i_1516_, lean_object* v_b_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1513_, v_as_1514_, v_sz_1515_, v_i_1516_, v_b_1517_, v___y_1518_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1524_, lean_object* v_as_1525_, lean_object* v_sz_1526_, lean_object* v_i_1527_, lean_object* v_b_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_instImplicit_boxed_1534_; size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v_instImplicit_boxed_1534_ = lean_unbox(v_instImplicit_1524_);
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1526_);
lean_dec(v_sz_1526_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1534_, v_as_1525_, v_sz_boxed_1535_, v_i_boxed_1536_, v_b_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec_ref(v_as_1525_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1538_, uint8_t v_s_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1538_, v_s_1539_, v___y_1541_, v___y_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1546_, lean_object* v_s_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_s_boxed_1553_; lean_object* v_res_1554_; 
v_s_boxed_1553_ = lean_unbox(v_s_1547_);
v_res_1554_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1546_, v_s_boxed_1553_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1555_, lean_object* v_ref_1556_, lean_object* v_msg_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1556_, v_msg_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_ref_1565_, lean_object* v_msg_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1564_, v_ref_1565_, v_msg_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v_ref_1565_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1573_, lean_object* v_x_1574_, uint8_t v_isExporting_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1574_, v_isExporting_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_x_1583_, lean_object* v_isExporting_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v_isExporting_boxed_1590_; lean_object* v_res_1591_; 
v_isExporting_boxed_1590_ = lean_unbox(v_isExporting_1584_);
v_res_1591_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1582_, v_x_1583_, v_isExporting_boxed_1590_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1592_, lean_object* v_x_1593_, uint8_t v_when_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1593_, v_when_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_x_1602_, lean_object* v_when_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_when_boxed_1609_; lean_object* v_res_1610_; 
v_when_boxed_1609_ = lean_unbox(v_when_1603_);
v_res_1610_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1601_, v_x_1602_, v_when_boxed_1609_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1611_, lean_object* v_projDecls_1612_, lean_object* v___x_1613_, lean_object* v___x_1614_, uint8_t v_instImplicit_1615_, lean_object* v___x_1616_, lean_object* v_params_1617_, lean_object* v_self_1618_, lean_object* v_a_1619_, lean_object* v___x_1620_, lean_object* v_n_1621_, lean_object* v___x_1622_, uint8_t v_a_1623_, lean_object* v_inst_1624_, lean_object* v_R_1625_, lean_object* v_a_1626_, lean_object* v_b_1627_, lean_object* v_c_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1611_, v_projDecls_1612_, v___x_1613_, v___x_1614_, v_instImplicit_1615_, v___x_1616_, v_params_1617_, v_self_1618_, v_a_1619_, v___x_1620_, v_n_1621_, v___x_1622_, v_a_1623_, v_a_1626_, v_b_1627_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1635_ = _args[0];
lean_object* v_projDecls_1636_ = _args[1];
lean_object* v___x_1637_ = _args[2];
lean_object* v___x_1638_ = _args[3];
lean_object* v_instImplicit_1639_ = _args[4];
lean_object* v___x_1640_ = _args[5];
lean_object* v_params_1641_ = _args[6];
lean_object* v_self_1642_ = _args[7];
lean_object* v_a_1643_ = _args[8];
lean_object* v___x_1644_ = _args[9];
lean_object* v_n_1645_ = _args[10];
lean_object* v___x_1646_ = _args[11];
lean_object* v_a_1647_ = _args[12];
lean_object* v_inst_1648_ = _args[13];
lean_object* v_R_1649_ = _args[14];
lean_object* v_a_1650_ = _args[15];
lean_object* v_b_1651_ = _args[16];
lean_object* v_c_1652_ = _args[17];
lean_object* v___y_1653_ = _args[18];
lean_object* v___y_1654_ = _args[19];
lean_object* v___y_1655_ = _args[20];
lean_object* v___y_1656_ = _args[21];
lean_object* v___y_1657_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1658_; uint8_t v_a_19160__boxed_1659_; lean_object* v_res_1660_; 
v_instImplicit_boxed_1658_ = lean_unbox(v_instImplicit_1639_);
v_a_19160__boxed_1659_ = lean_unbox(v_a_1647_);
v_res_1660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1635_, v_projDecls_1636_, v___x_1637_, v___x_1638_, v_instImplicit_boxed_1658_, v___x_1640_, v_params_1641_, v_self_1642_, v_a_1643_, v___x_1644_, v_n_1645_, v___x_1646_, v_a_19160__boxed_1659_, v_inst_1648_, v_R_1649_, v_a_1650_, v_b_1651_, v_c_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_projDecls_1636_);
lean_dec(v_upperBound_1635_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1661_, uint8_t v_allowLevelAssignments_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1662_, v_k_1661_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1668_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1668_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1685_, lean_object* v_allowLevelAssignments_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1692_; lean_object* v_res_1693_; 
v_allowLevelAssignments_boxed_1692_ = lean_unbox(v_allowLevelAssignments_1686_);
v_res_1693_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1685_, v_allowLevelAssignments_boxed_1692_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1694_, lean_object* v_k_1695_, uint8_t v_allowLevelAssignments_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1695_, v_allowLevelAssignments_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_k_1704_, lean_object* v_allowLevelAssignments_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1711_; lean_object* v_res_1712_; 
v_allowLevelAssignments_boxed_1711_ = lean_unbox(v_allowLevelAssignments_1705_);
v_res_1712_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1703_, v_k_1704_, v_allowLevelAssignments_boxed_1711_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1713_, size_t v_sz_1714_, size_t v_i_1715_, lean_object* v_b_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_usize_dec_lt(v_i_1715_, v_sz_1714_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v_b_1716_);
return v___x_1723_;
}
else
{
lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1779_; 
v_snd_1724_ = lean_ctor_get(v_b_1716_, 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_b_1716_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_b_1716_, 0);
lean_dec(v_unused_1780_);
v___x_1726_ = v_b_1716_;
v_isShared_1727_ = v_isSharedCheck_1779_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_dec(v_b_1716_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1779_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_array_1728_; lean_object* v_start_1729_; lean_object* v_stop_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v_array_1728_ = lean_ctor_get(v_snd_1724_, 0);
v_start_1729_ = lean_ctor_get(v_snd_1724_, 1);
v_stop_1730_ = lean_ctor_get(v_snd_1724_, 2);
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_nat_dec_lt(v_start_1729_, v_stop_1730_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1734_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1731_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_snd_1724_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
else
{
lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1775_; 
lean_inc(v_stop_1730_);
lean_inc(v_start_1729_);
lean_inc_ref(v_array_1728_);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_snd_1724_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; 
v_unused_1776_ = lean_ctor_get(v_snd_1724_, 2);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_snd_1724_, 1);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_snd_1724_, 0);
lean_dec(v_unused_1778_);
v___x_1738_ = v_snd_1724_;
v_isShared_1739_ = v_isSharedCheck_1775_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v_snd_1724_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1775_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v_a_1740_ = lean_array_uget_borrowed(v_as_1713_, v_i_1715_);
v___x_1741_ = lean_array_fget(v_array_1728_, v_start_1729_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_start_1729_, v___x_1742_);
lean_dec(v_start_1729_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___x_1743_);
v___x_1745_ = v___x_1738_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_array_1728_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_stop_1730_);
v___x_1745_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; 
lean_inc(v_a_1740_);
v___x_1746_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1740_, v___x_1741_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1765_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1765_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1765_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_unbox(v_a_1747_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_a_1747_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1745_);
lean_ctor_set(v___x_1726_, 0, v___x_1752_);
v___x_1754_ = v___x_1726_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1745_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1754_);
v___x_1756_ = v___x_1749_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v___x_1760_; 
lean_del_object(v___x_1749_);
lean_dec(v_a_1747_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1745_);
lean_ctor_set(v___x_1726_, 0, v___x_1731_);
v___x_1760_ = v___x_1726_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1745_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1715_, v___x_1761_);
v_i_1715_ = v___x_1762_;
v_b_1716_ = v___x_1760_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___x_1745_);
lean_del_object(v___x_1726_);
v_a_1766_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1746_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1746_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1781_, lean_object* v_sz_1782_, lean_object* v_i_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1782_);
lean_dec(v_sz_1782_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1783_);
lean_dec(v_i_1783_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1781_, v_sz_boxed_1790_, v_i_boxed_1791_, v_b_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_as_1781_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1793_, lean_object* v_params2_1794_, lean_object* v___x_1795_, lean_object* v_params1_1796_, uint8_t v___x_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
if (v___x_1793_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v___x_1795_);
lean_dec_ref(v_params2_1794_);
v___x_1803_ = lean_box(v___x_1793_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; size_t v_sz_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = l_Array_toSubarray___redArg(v_params2_1794_, v___x_1805_, v___x_1795_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___x_1806_);
v_sz_1809_ = lean_array_size(v_params1_1796_);
v___x_1810_ = ((size_t)0ULL);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1796_, v_sz_1809_, v___x_1810_, v___x_1808_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1825_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_fst_1816_; 
v_fst_1816_ = lean_ctor_get(v_a_1812_, 0);
lean_inc(v_fst_1816_);
lean_dec(v_a_1812_);
if (lean_obj_tag(v_fst_1816_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_box(v___x_1797_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1817_);
v___x_1819_ = v___x_1814_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
else
{
lean_object* v_val_1821_; lean_object* v___x_1823_; 
v_val_1821_ = lean_ctor_get(v_fst_1816_, 0);
lean_inc(v_val_1821_);
lean_dec_ref_known(v_fst_1816_, 1);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_val_1821_);
v___x_1823_ = v___x_1814_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_val_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1811_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1811_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1834_, lean_object* v_params2_1835_, lean_object* v___x_1836_, lean_object* v_params1_1837_, lean_object* v___x_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
uint8_t v___x_2007__boxed_1844_; uint8_t v___x_2009__boxed_1845_; lean_object* v_res_1846_; 
v___x_2007__boxed_1844_ = lean_unbox(v___x_1834_);
v___x_2009__boxed_1845_ = lean_unbox(v___x_1838_);
v_res_1846_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1844_, v_params2_1835_, v___x_1836_, v_params1_1837_, v___x_2009__boxed_1845_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_params1_1837_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1847_, lean_object* v_params2_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___y_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1854_ = lean_array_get_size(v_params1_1847_);
v___x_1855_ = lean_array_get_size(v_params2_1848_);
v___x_1856_ = lean_nat_dec_eq(v___x_1854_, v___x_1855_);
v___x_1857_ = 1;
v___x_1858_ = lean_box(v___x_1856_);
v___x_1859_ = lean_box(v___x_1857_);
v___y_1860_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1860_, 0, v___x_1858_);
lean_closure_set(v___y_1860_, 1, v_params2_1848_);
lean_closure_set(v___y_1860_, 2, v___x_1855_);
lean_closure_set(v___y_1860_, 3, v_params1_1847_);
lean_closure_set(v___y_1860_, 4, v___x_1859_);
v___x_1861_ = 0;
v___x_1862_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1860_, v___x_1861_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1863_, lean_object* v_params2_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1863_, v_params2_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v_env_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1874_ = lean_st_ref_get(v___y_1872_);
v_env_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_ref(v_env_1875_);
lean_dec(v___x_1874_);
v___x_1876_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1875_, v_declName_1871_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1878_, v___y_1879_);
lean_dec(v___y_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1882_, v___y_1886_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1896_; lean_object* v_dummy_1897_; 
v___x_1896_ = lean_box(0);
v_dummy_1897_ = l_Lean_Expr_sort___override(v___x_1896_);
return v_dummy_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1898_, lean_object* v_induct_1899_, lean_object* v_params_1900_, lean_object* v_idx_1901_, lean_object* v_e_1902_, lean_object* v_x_x3f_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
if (lean_obj_tag(v_e_1902_) == 11)
{
lean_object* v_typeName_1915_; lean_object* v_idx_1916_; lean_object* v_struct_1917_; uint8_t v___x_1964_; 
v_typeName_1915_ = lean_ctor_get(v_e_1902_, 0);
v_idx_1916_ = lean_ctor_get(v_e_1902_, 1);
v_struct_1917_ = lean_ctor_get(v_e_1902_, 2);
lean_inc_ref(v_struct_1917_);
v___x_1964_ = lean_nat_dec_eq(v_idx_1916_, v_idx_1901_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v_struct_1917_);
lean_dec_ref_known(v_e_1902_, 3);
lean_dec_ref(v_params_1900_);
goto v___jp_1912_;
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_name_eq(v_induct_1899_, v_typeName_1915_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_struct_1917_);
lean_dec_ref_known(v_e_1902_, 3);
lean_dec_ref(v_params_1900_);
goto v___jp_1912_;
}
else
{
if (lean_obj_tag(v_x_x3f_1903_) == 0)
{
goto v___jp_1918_;
}
else
{
lean_object* v_val_1966_; uint8_t v___x_1967_; 
v_val_1966_ = lean_ctor_get(v_x_x3f_1903_, 0);
v___x_1967_ = lean_expr_eqv(v_val_1966_, v_struct_1917_);
if (v___x_1967_ == 0)
{
lean_dec_ref(v_struct_1917_);
lean_dec_ref_known(v_e_1902_, 3);
lean_dec_ref(v_params_1900_);
goto v___jp_1912_;
}
else
{
goto v___jp_1918_;
}
}
}
}
v___jp_1918_:
{
lean_object* v___x_1919_; 
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
v___x_1919_ = lean_infer_type(v_e_1902_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
v___x_1921_ = lean_whnf(v_a_1920_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_dummy_1923_; lean_object* v_nargs_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v_dummy_1923_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1924_ = l_Lean_Expr_getAppNumArgs(v_a_1922_);
lean_inc(v_nargs_1924_);
v___x_1925_ = lean_mk_array(v_nargs_1924_, v_dummy_1923_);
v___x_1926_ = lean_unsigned_to_nat(1u);
v___x_1927_ = lean_nat_sub(v_nargs_1924_, v___x_1926_);
lean_dec(v_nargs_1924_);
v___x_1928_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1922_, v___x_1925_, v___x_1927_);
v___x_1929_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1900_, v___x_1928_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1939_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_unbox(v_a_1930_);
lean_dec(v_a_1930_);
if (v___x_1934_ == 0)
{
lean_del_object(v___x_1932_);
lean_dec_ref(v_struct_1917_);
goto v___jp_1912_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_struct_1917_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_struct_1917_);
v_a_1940_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1929_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1929_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_struct_1917_);
lean_dec_ref(v_params_1900_);
v_a_1948_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1921_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1921_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_struct_1917_);
lean_dec_ref(v_params_1900_);
v_a_1956_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1919_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1919_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
else
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Expr_getAppFn(v_e_1902_);
if (lean_obj_tag(v___x_1968_) == 4)
{
lean_object* v_declName_1969_; lean_object* v___x_1970_; lean_object* v_a_1971_; 
v_declName_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_declName_1969_);
lean_dec_ref_known(v___x_1968_, 2);
v___x_1970_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1969_, v_a_1907_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
if (lean_obj_tag(v_a_1971_) == 1)
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2016_; 
v_val_1972_ = lean_ctor_get(v_a_1971_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1974_ = v_a_1971_;
v_isShared_1975_ = v_isSharedCheck_2016_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v_a_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2016_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_ctorName_1976_; lean_object* v_numParams_1977_; lean_object* v_i_1978_; uint8_t v___x_1979_; 
v_ctorName_1976_ = lean_ctor_get(v_val_1972_, 0);
lean_inc(v_ctorName_1976_);
v_numParams_1977_ = lean_ctor_get(v_val_1972_, 1);
lean_inc(v_numParams_1977_);
v_i_1978_ = lean_ctor_get(v_val_1972_, 2);
lean_inc(v_i_1978_);
lean_dec(v_val_1972_);
v___x_1979_ = lean_name_eq(v_ctorName_1976_, v_ctor_1898_);
lean_dec(v_ctorName_1976_);
if (v___x_1979_ == 0)
{
lean_dec(v_i_1978_);
lean_dec(v_numParams_1977_);
lean_del_object(v___x_1974_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
else
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_nat_dec_eq(v_i_1978_, v_idx_1901_);
lean_dec(v_i_1978_);
if (v___x_1980_ == 0)
{
lean_dec(v_numParams_1977_);
lean_del_object(v___x_1974_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1981_ = l_Lean_Expr_getAppNumArgs(v_e_1902_);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_numParams_1977_, v___x_1982_);
lean_dec(v_numParams_1977_);
v___x_1984_ = lean_nat_dec_eq(v___x_1981_, v___x_1983_);
lean_dec(v___x_1983_);
lean_dec(v___x_1981_);
if (v___x_1984_ == 0)
{
lean_del_object(v___x_1974_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_Expr_appArg_x21(v_e_1902_);
if (lean_obj_tag(v_x_x3f_1903_) == 0)
{
goto v___jp_1986_;
}
else
{
lean_object* v_val_2014_; uint8_t v___x_2015_; 
v_val_2014_ = lean_ctor_get(v_x_x3f_1903_, 0);
v___x_2015_ = lean_expr_eqv(v_val_2014_, v___x_1985_);
if (v___x_2015_ == 0)
{
lean_dec_ref(v___x_1985_);
lean_del_object(v___x_1974_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
else
{
goto v___jp_1986_;
}
}
v___jp_1986_:
{
lean_object* v___x_1987_; lean_object* v_dummy_1988_; lean_object* v_nargs_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = l_Lean_Expr_appFn_x21(v_e_1902_);
lean_dec_ref(v_e_1902_);
v_dummy_1988_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1989_ = l_Lean_Expr_getAppNumArgs(v___x_1987_);
lean_inc(v_nargs_1989_);
v___x_1990_ = lean_mk_array(v_nargs_1989_, v_dummy_1988_);
v___x_1991_ = lean_nat_sub(v_nargs_1989_, v___x_1982_);
lean_dec(v_nargs_1989_);
v___x_1992_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1987_, v___x_1990_, v___x_1991_);
v___x_1993_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1900_, v___x_1992_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
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
lean_dec_ref(v___x_1985_);
lean_del_object(v___x_1974_);
goto v___jp_1909_;
}
else
{
lean_object* v___x_2000_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1985_);
v___x_2000_ = v___x_1974_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1985_);
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
lean_dec_ref(v___x_1985_);
lean_del_object(v___x_1974_);
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
}
}
}
else
{
lean_dec(v_a_1971_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
}
else
{
lean_dec_ref(v___x_1968_);
lean_dec_ref(v_e_1902_);
lean_dec_ref(v_params_1900_);
goto v___jp_1909_;
}
}
v___jp_1909_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
v___jp_1912_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2017_, lean_object* v_induct_2018_, lean_object* v_params_2019_, lean_object* v_idx_2020_, lean_object* v_e_2021_, lean_object* v_x_x3f_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2017_, v_induct_2018_, v_params_2019_, v_idx_2020_, v_e_2021_, v_x_x3f_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_x_x3f_2022_);
lean_dec(v_idx_2020_);
lean_dec(v_induct_2018_);
lean_dec(v_ctor_2017_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_env_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2035_ = lean_st_ref_get(v___y_2033_);
v_env_2039_ = lean_ctor_get(v___x_2035_, 0);
lean_inc_ref(v_env_2039_);
lean_dec(v___x_2035_);
v___x_2040_ = 0;
v___x_2041_ = l_Lean_Environment_findAsync_x3f(v_env_2039_, v_constName_2029_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2061_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2061_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2061_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint8_t v_kind_2046_; 
v_kind_2046_ = lean_ctor_get_uint8(v_val_2042_, sizeof(void*)*3);
if (v_kind_2046_ == 6)
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2042_);
if (lean_obj_tag(v___x_2047_) == 6)
{
lean_object* v_val_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2058_; 
v_val_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_val_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_val_2048_);
v___x_2053_ = v___x_2044_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_val_2048_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2055_ = v___x_2050_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_dec_ref(v___x_2047_);
lean_del_object(v___x_2044_);
v___x_2059_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2060_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2059_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
return v___x_2060_;
}
}
else
{
lean_del_object(v___x_2044_);
lean_dec(v_val_2042_);
goto v___jp_2036_;
}
}
}
else
{
lean_dec(v___x_2041_);
goto v___jp_2036_;
}
v___jp_2036_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, lean_object* v_declName_2080_, lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v_a_2083_, lean_object* v_val_2084_, lean_object* v_a_2085_, lean_object* v_b_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_nat_dec_lt(v_a_2085_, v_upperBound_2077_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec(v_a_2085_);
lean_dec_ref(v___x_2082_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2086_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec_ref(v_b_2086_);
v___x_2094_ = l_Lean_instInhabitedExpr;
v___x_2095_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2096_ = lean_nat_add(v___x_2078_, v_a_2085_);
v___x_2097_ = lean_array_get_borrowed(v___x_2094_, v___x_2079_, v___x_2096_);
lean_dec(v___x_2096_);
lean_inc(v___x_2097_);
lean_inc_ref(v___x_2082_);
v___x_2098_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2080_, v___x_2081_, v___x_2082_, v_a_2085_, v___x_2097_, v_a_2083_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2116_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2116_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2116_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
if (lean_obj_tag(v_a_2099_) == 1)
{
lean_object* v_val_2103_; uint8_t v___x_2104_; 
v_val_2103_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v_a_2099_, 1);
v___x_2104_ = lean_expr_eqv(v_val_2103_, v_val_2084_);
lean_dec(v_val_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec(v_a_2085_);
lean_dec_ref(v___x_2082_);
v___x_2105_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2105_);
v___x_2107_ = v___x_2101_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_del_object(v___x_2101_);
v___x_2109_ = lean_unsigned_to_nat(1u);
v___x_2110_ = lean_nat_add(v_a_2085_, v___x_2109_);
lean_dec(v_a_2085_);
v_a_2085_ = v___x_2110_;
v_b_2086_ = v___x_2095_;
goto _start;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec(v_a_2099_);
lean_dec(v_a_2085_);
lean_dec_ref(v___x_2082_);
v___x_2112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2112_);
v___x_2114_ = v___x_2101_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_a_2085_);
lean_dec_ref(v___x_2082_);
v_a_2117_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2098_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2098_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2125_, lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_declName_2128_, lean_object* v___x_2129_, lean_object* v___x_2130_, lean_object* v_a_2131_, lean_object* v_val_2132_, lean_object* v_a_2133_, lean_object* v_b_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2125_, v___x_2126_, v___x_2127_, v_declName_2128_, v___x_2129_, v___x_2130_, v_a_2131_, v_val_2132_, v_a_2133_, v_b_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v_val_2132_);
lean_dec(v_a_2131_);
lean_dec(v___x_2129_);
lean_dec(v_declName_2128_);
lean_dec_ref(v___x_2127_);
lean_dec(v___x_2126_);
lean_dec(v_upperBound_2125_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2141_, lean_object* v_p_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Expr_getAppFn(v_e_2141_);
if (lean_obj_tag(v___x_2148_) == 4)
{
lean_object* v_declName_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_declName_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_n(v_declName_2149_, 2);
lean_dec_ref_known(v___x_2148_, 2);
v___x_2150_ = l_Lean_instInhabitedExpr;
v___x_2151_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2149_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2223_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2223_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2223_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
if (lean_obj_tag(v_a_2152_) == 1)
{
lean_object* v_val_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2220_; 
v_val_2161_ = lean_ctor_get(v_a_2152_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2163_ = v_a_2152_;
v_isShared_2164_ = v_isSharedCheck_2220_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_val_2161_);
lean_dec(v_a_2152_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2220_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_induct_2165_; lean_object* v_numParams_2166_; lean_object* v_numFields_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v_induct_2165_ = lean_ctor_get(v_val_2161_, 1);
lean_inc_n(v_induct_2165_, 2);
v_numParams_2166_ = lean_ctor_get(v_val_2161_, 3);
lean_inc(v_numParams_2166_);
v_numFields_2167_ = lean_ctor_get(v_val_2161_, 4);
lean_inc(v_numFields_2167_);
lean_dec(v_val_2161_);
v___x_2168_ = lean_apply_1(v_p_2142_, v_induct_2165_);
v___x_2169_ = lean_unbox(v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_dec(v_numFields_2167_);
lean_dec(v_numParams_2166_);
lean_dec(v_induct_2165_);
lean_del_object(v___x_2154_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_e_2141_);
v___x_2170_ = lean_box(0);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2170_);
v___x_2172_ = v___x_2163_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
lean_del_object(v___x_2163_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_nat_dec_lt(v___x_2174_, v_numFields_2167_);
if (v___x_2175_ == 0)
{
lean_dec(v_numFields_2167_);
lean_dec(v_numParams_2166_);
lean_dec(v_induct_2165_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_e_2141_);
goto v___jp_2156_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = l_Lean_Expr_getAppNumArgs(v_e_2141_);
v___x_2177_ = lean_nat_add(v_numParams_2166_, v_numFields_2167_);
v___x_2178_ = lean_nat_dec_eq(v___x_2176_, v___x_2177_);
lean_dec(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_dec(v___x_2176_);
lean_dec(v_numFields_2167_);
lean_dec(v_numParams_2166_);
lean_dec(v_induct_2165_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_e_2141_);
goto v___jp_2156_;
}
else
{
lean_object* v_dummy_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_del_object(v___x_2154_);
v_dummy_2179_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2176_);
v___x_2180_ = lean_mk_array(v___x_2176_, v_dummy_2179_);
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_sub(v___x_2176_, v___x_2181_);
lean_dec(v___x_2176_);
v___x_2183_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2141_, v___x_2180_, v___x_2182_);
lean_inc(v_numParams_2166_);
v___x_2184_ = l_Array_extract___redArg(v___x_2183_, v___x_2174_, v_numParams_2166_);
v___x_2185_ = lean_array_get_borrowed(v___x_2150_, v___x_2183_, v_numParams_2166_);
v___x_2186_ = lean_box(0);
lean_inc(v___x_2185_);
lean_inc_ref(v___x_2184_);
v___x_2187_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2149_, v_induct_2165_, v___x_2184_, v___x_2174_, v___x_2185_, v___x_2186_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2219_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2219_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2219_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_del_object(v___x_2190_);
v_val_2192_ = lean_ctor_get(v_a_2188_, 0);
v___x_2193_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2167_, v_numParams_2166_, v___x_2183_, v_declName_2149_, v_induct_2165_, v___x_2184_, v_a_2188_, v_val_2192_, v___x_2181_, v___x_2193_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_induct_2165_);
lean_dec(v_declName_2149_);
lean_dec_ref(v___x_2183_);
lean_dec(v_numParams_2166_);
lean_dec(v_numFields_2167_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2207_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2207_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2207_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_fst_2199_; 
v_fst_2199_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_fst_2199_);
lean_dec(v_a_2195_);
if (lean_obj_tag(v_fst_2199_) == 0)
{
lean_object* v___x_2201_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_a_2188_);
v___x_2201_ = v___x_2197_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2188_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
else
{
lean_object* v_val_2203_; lean_object* v___x_2205_; 
lean_dec_ref_known(v_a_2188_, 1);
v_val_2203_ = lean_ctor_get(v_fst_2199_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v_fst_2199_, 1);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_val_2203_);
v___x_2205_ = v___x_2197_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_val_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref_known(v_a_2188_, 1);
v_a_2208_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2194_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2194_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
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
lean_object* v___x_2217_; 
lean_dec(v_a_2188_);
lean_dec_ref(v___x_2184_);
lean_dec_ref(v___x_2183_);
lean_dec(v_numFields_2167_);
lean_dec(v_numParams_2166_);
lean_dec(v_induct_2165_);
lean_dec(v_declName_2149_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2186_);
v___x_2217_ = v___x_2190_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2186_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_dec_ref(v___x_2184_);
lean_dec_ref(v___x_2183_);
lean_dec(v_numFields_2167_);
lean_dec(v_numParams_2166_);
lean_dec(v_induct_2165_);
lean_dec(v_declName_2149_);
return v___x_2187_;
}
}
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_del_object(v___x_2154_);
lean_dec(v_a_2152_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_p_2142_);
lean_dec_ref(v_e_2141_);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
v___jp_2156_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2157_);
v___x_2159_ = v___x_2154_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_declName_2149_);
lean_dec_ref(v_p_2142_);
lean_dec_ref(v_e_2141_);
v_a_2224_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2151_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2151_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v___x_2148_);
lean_dec_ref(v_p_2142_);
lean_dec_ref(v_e_2141_);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2234_, lean_object* v_p_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_etaStruct_x3f(v_e_2234_, v_p_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2242_, lean_object* v___x_2243_, lean_object* v___x_2244_, lean_object* v_declName_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_a_2248_, lean_object* v_val_2249_, lean_object* v_inst_2250_, lean_object* v_R_2251_, lean_object* v_a_2252_, lean_object* v_b_2253_, lean_object* v_c_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2242_, v___x_2243_, v___x_2244_, v_declName_2245_, v___x_2246_, v___x_2247_, v_a_2248_, v_val_2249_, v_a_2252_, v_b_2253_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2261_ = _args[0];
lean_object* v___x_2262_ = _args[1];
lean_object* v___x_2263_ = _args[2];
lean_object* v_declName_2264_ = _args[3];
lean_object* v___x_2265_ = _args[4];
lean_object* v___x_2266_ = _args[5];
lean_object* v_a_2267_ = _args[6];
lean_object* v_val_2268_ = _args[7];
lean_object* v_inst_2269_ = _args[8];
lean_object* v_R_2270_ = _args[9];
lean_object* v_a_2271_ = _args[10];
lean_object* v_b_2272_ = _args[11];
lean_object* v_c_2273_ = _args[12];
lean_object* v___y_2274_ = _args[13];
lean_object* v___y_2275_ = _args[14];
lean_object* v___y_2276_ = _args[15];
lean_object* v___y_2277_ = _args[16];
lean_object* v___y_2278_ = _args[17];
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2261_, v___x_2262_, v___x_2263_, v_declName_2264_, v___x_2265_, v___x_2266_, v_a_2267_, v_val_2268_, v_inst_2269_, v_R_2270_, v_a_2271_, v_b_2272_, v_c_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_val_2268_);
lean_dec(v_a_2267_);
lean_dec(v___x_2265_);
lean_dec(v_declName_2264_);
lean_dec_ref(v___x_2263_);
lean_dec(v___x_2262_);
lean_dec(v_upperBound_2261_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = l_Lean_Expr_hasMVar(v_e_2280_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_e_2280_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v_mctx_2286_; lean_object* v___x_2287_; lean_object* v_fst_2288_; lean_object* v_snd_2289_; lean_object* v___x_2290_; lean_object* v_cache_2291_; lean_object* v_zetaDeltaFVarIds_2292_; lean_object* v_postponed_2293_; lean_object* v_diag_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2303_; 
v___x_2285_ = lean_st_ref_get(v___y_2281_);
v_mctx_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_ref(v_mctx_2286_);
lean_dec(v___x_2285_);
v___x_2287_ = l_Lean_instantiateMVarsCore(v_mctx_2286_, v_e_2280_);
v_fst_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_fst_2288_);
v_snd_2289_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_snd_2289_);
lean_dec_ref(v___x_2287_);
v___x_2290_ = lean_st_ref_take(v___y_2281_);
v_cache_2291_ = lean_ctor_get(v___x_2290_, 1);
v_zetaDeltaFVarIds_2292_ = lean_ctor_get(v___x_2290_, 2);
v_postponed_2293_ = lean_ctor_get(v___x_2290_, 3);
v_diag_2294_ = lean_ctor_get(v___x_2290_, 4);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v___x_2290_, 0);
lean_dec(v_unused_2304_);
v___x_2296_ = v___x_2290_;
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_diag_2294_);
lean_inc(v_postponed_2293_);
lean_inc(v_zetaDeltaFVarIds_2292_);
lean_inc(v_cache_2291_);
lean_dec(v___x_2290_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_snd_2289_);
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_snd_2289_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_cache_2291_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_zetaDeltaFVarIds_2292_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_postponed_2293_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_diag_2294_);
v___x_2299_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_st_ref_put(v___y_2281_, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_fst_2288_);
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2305_, v___y_2306_);
lean_dec(v___y_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2309_, v___y_2311_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v_x_2333_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2340_, lean_object* v_e_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_Meta_etaStruct_x3f(v_e_2341_, v_p_2340_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2367_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2367_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2367_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v_val_2352_ = lean_ctor_get(v_a_2348_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2354_ = v_a_2348_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_val_2352_);
lean_dec(v_a_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 0);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_val_2352_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2357_);
v___x_2359_ = v___x_2350_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_dec(v_a_2348_);
v___x_2363_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2363_);
v___x_2365_ = v___x_2350_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2347_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2347_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2376_, lean_object* v_e_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2376_, v_e_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2384_, lean_object* v_x_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_apply_1(v_x_2385_, lean_box(0));
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2393_, v_x_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2401_, lean_object* v_b_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 0)
{
lean_dec(v_b_2402_);
lean_dec_ref(v_a_2401_);
return v_x_2403_;
}
else
{
lean_object* v_key_2404_; lean_object* v_value_2405_; lean_object* v_tail_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2418_; 
v_key_2404_ = lean_ctor_get(v_x_2403_, 0);
v_value_2405_ = lean_ctor_get(v_x_2403_, 1);
v_tail_2406_ = lean_ctor_get(v_x_2403_, 2);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_x_2403_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2408_ = v_x_2403_;
v_isShared_2409_ = v_isSharedCheck_2418_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_tail_2406_);
lean_inc(v_value_2405_);
lean_inc(v_key_2404_);
lean_dec(v_x_2403_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2418_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
uint8_t v___x_2410_; 
v___x_2410_ = l_Lean_ExprStructEq_beq(v_key_2404_, v_a_2401_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2411_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2401_, v_b_2402_, v_tail_2406_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 2, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_key_2404_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_value_2405_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
else
{
lean_object* v___x_2416_; 
lean_dec(v_value_2405_);
lean_dec(v_key_2404_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v_b_2402_);
lean_ctor_set(v___x_2408_, 0, v_a_2401_);
v___x_2416_ = v___x_2408_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2401_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_b_2402_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_tail_2406_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2419_, lean_object* v_x_2420_){
_start:
{
if (lean_obj_tag(v_x_2420_) == 0)
{
return v_x_2419_;
}
else
{
lean_object* v_key_2421_; lean_object* v_value_2422_; lean_object* v_tail_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2446_; 
v_key_2421_ = lean_ctor_get(v_x_2420_, 0);
v_value_2422_ = lean_ctor_get(v_x_2420_, 1);
v_tail_2423_ = lean_ctor_get(v_x_2420_, 2);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_x_2420_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2425_ = v_x_2420_;
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_tail_2423_);
lean_inc(v_value_2422_);
lean_inc(v_key_2421_);
lean_dec(v_x_2420_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; uint64_t v___x_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v_fold_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; uint64_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2427_ = lean_array_get_size(v_x_2419_);
v___x_2428_ = l_Lean_ExprStructEq_hash(v_key_2421_);
v___x_2429_ = 32ULL;
v___x_2430_ = lean_uint64_shift_right(v___x_2428_, v___x_2429_);
v_fold_2431_ = lean_uint64_xor(v___x_2428_, v___x_2430_);
v___x_2432_ = 16ULL;
v___x_2433_ = lean_uint64_shift_right(v_fold_2431_, v___x_2432_);
v___x_2434_ = lean_uint64_xor(v_fold_2431_, v___x_2433_);
v___x_2435_ = lean_uint64_to_usize(v___x_2434_);
v___x_2436_ = lean_usize_of_nat(v___x_2427_);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_sub(v___x_2436_, v___x_2437_);
v___x_2439_ = lean_usize_land(v___x_2435_, v___x_2438_);
v___x_2440_ = lean_array_uget_borrowed(v_x_2419_, v___x_2439_);
lean_inc(v___x_2440_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 2, v___x_2440_);
v___x_2442_ = v___x_2425_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_key_2421_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_value_2422_);
lean_ctor_set(v_reuseFailAlloc_2445_, 2, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_array_uset(v_x_2419_, v___x_2439_, v___x_2442_);
v_x_2419_ = v___x_2443_;
v_x_2420_ = v_tail_2423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2447_, lean_object* v_source_2448_, lean_object* v_target_2449_){
_start:
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = lean_array_get_size(v_source_2448_);
v___x_2451_ = lean_nat_dec_lt(v_i_2447_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec_ref(v_source_2448_);
lean_dec(v_i_2447_);
return v_target_2449_;
}
else
{
lean_object* v_es_2452_; lean_object* v___x_2453_; lean_object* v_source_2454_; lean_object* v_target_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_es_2452_ = lean_array_fget(v_source_2448_, v_i_2447_);
v___x_2453_ = lean_box(0);
v_source_2454_ = lean_array_fset(v_source_2448_, v_i_2447_, v___x_2453_);
v_target_2455_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2449_, v_es_2452_);
v___x_2456_ = lean_unsigned_to_nat(1u);
v___x_2457_ = lean_nat_add(v_i_2447_, v___x_2456_);
lean_dec(v_i_2447_);
v_i_2447_ = v___x_2457_;
v_source_2448_ = v_source_2454_;
v_target_2449_ = v_target_2455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2459_){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_nbuckets_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2460_ = lean_array_get_size(v_data_2459_);
v___x_2461_ = lean_unsigned_to_nat(2u);
v_nbuckets_2462_ = lean_nat_mul(v___x_2460_, v___x_2461_);
v___x_2463_ = lean_unsigned_to_nat(0u);
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_mk_array(v_nbuckets_2462_, v___x_2464_);
v___x_2466_ = lean_array_propagate_mark(v_data_2459_, v___x_2465_);
v___x_2467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2463_, v_data_2459_, v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2468_, lean_object* v_x_2469_){
_start:
{
if (lean_obj_tag(v_x_2469_) == 0)
{
uint8_t v___x_2470_; 
v___x_2470_ = 0;
return v___x_2470_;
}
else
{
lean_object* v_key_2471_; lean_object* v_tail_2472_; uint8_t v___x_2473_; 
v_key_2471_ = lean_ctor_get(v_x_2469_, 0);
v_tail_2472_ = lean_ctor_get(v_x_2469_, 2);
v___x_2473_ = l_Lean_ExprStructEq_beq(v_key_2471_, v_a_2468_);
if (v___x_2473_ == 0)
{
v_x_2469_ = v_tail_2472_;
goto _start;
}
else
{
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2475_, lean_object* v_x_2476_){
_start:
{
uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_res_2477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2475_, v_x_2476_);
lean_dec(v_x_2476_);
lean_dec_ref(v_a_2475_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2479_, lean_object* v_a_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v_size_2482_; lean_object* v_buckets_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2526_; 
v_size_2482_ = lean_ctor_get(v_m_2479_, 0);
v_buckets_2483_ = lean_ctor_get(v_m_2479_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_m_2479_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2485_ = v_m_2479_;
v_isShared_2486_ = v_isSharedCheck_2526_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_buckets_2483_);
lean_inc(v_size_2482_);
lean_dec(v_m_2479_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2526_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v_fold_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; lean_object* v_bkt_2500_; uint8_t v___x_2501_; 
v___x_2487_ = lean_array_get_size(v_buckets_2483_);
v___x_2488_ = l_Lean_ExprStructEq_hash(v_a_2480_);
v___x_2489_ = 32ULL;
v___x_2490_ = lean_uint64_shift_right(v___x_2488_, v___x_2489_);
v_fold_2491_ = lean_uint64_xor(v___x_2488_, v___x_2490_);
v___x_2492_ = 16ULL;
v___x_2493_ = lean_uint64_shift_right(v_fold_2491_, v___x_2492_);
v___x_2494_ = lean_uint64_xor(v_fold_2491_, v___x_2493_);
v___x_2495_ = lean_uint64_to_usize(v___x_2494_);
v___x_2496_ = lean_usize_of_nat(v___x_2487_);
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_sub(v___x_2496_, v___x_2497_);
v___x_2499_ = lean_usize_land(v___x_2495_, v___x_2498_);
v_bkt_2500_ = lean_array_uget_borrowed(v_buckets_2483_, v___x_2499_);
v___x_2501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2480_, v_bkt_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v_size_x27_2503_; lean_object* v___x_2504_; lean_object* v_buckets_x27_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2502_ = lean_unsigned_to_nat(1u);
v_size_x27_2503_ = lean_nat_add(v_size_2482_, v___x_2502_);
lean_dec(v_size_2482_);
lean_inc(v_bkt_2500_);
v___x_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2480_);
lean_ctor_set(v___x_2504_, 1, v_b_2481_);
lean_ctor_set(v___x_2504_, 2, v_bkt_2500_);
v_buckets_x27_2505_ = lean_array_uset(v_buckets_2483_, v___x_2499_, v___x_2504_);
v___x_2506_ = lean_unsigned_to_nat(4u);
v___x_2507_ = lean_nat_mul(v_size_x27_2503_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(3u);
v___x_2509_ = lean_nat_div(v___x_2507_, v___x_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_array_get_size(v_buckets_x27_2505_);
v___x_2511_ = lean_nat_dec_le(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
if (v___x_2511_ == 0)
{
lean_object* v_val_2512_; lean_object* v___x_2514_; 
v_val_2512_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2505_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v_val_2512_);
lean_ctor_set(v___x_2485_, 0, v_size_x27_2503_);
v___x_2514_ = v___x_2485_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_val_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
else
{
lean_object* v___x_2517_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v_buckets_x27_2505_);
lean_ctor_set(v___x_2485_, 0, v_size_x27_2503_);
v___x_2517_ = v___x_2485_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_buckets_x27_2505_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v___x_2519_; lean_object* v_buckets_x27_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_inc(v_bkt_2500_);
v___x_2519_ = lean_box(0);
v_buckets_x27_2520_ = lean_array_uset(v_buckets_2483_, v___x_2499_, v___x_2519_);
v___x_2521_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2480_, v_b_2481_, v_bkt_2500_);
v___x_2522_ = lean_array_uset(v_buckets_x27_2520_, v___x_2499_, v___x_2521_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 1, v___x_2522_);
v___x_2524_ = v___x_2485_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_size_2482_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2527_, lean_object* v_e_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2531_ = lean_st_ref_take(v_a_2527_);
v___x_2532_ = lean_box(0);
v___x_2533_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2531_, v_e_2528_, v_a_2529_);
v___x_2534_ = lean_st_ref_put(v_a_2527_, v___x_2533_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2535_, lean_object* v_e_2536_, lean_object* v_a_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2535_, v_e_2536_, v_a_2537_);
lean_dec(v_a_2535_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2540_, lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_apply_1(v_x_2541_, lean_box(0));
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2549_, lean_object* v_x_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2549_, v_x_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2557_, lean_object* v_x_2558_){
_start:
{
if (lean_obj_tag(v_x_2558_) == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_box(0);
return v___x_2559_;
}
else
{
lean_object* v_key_2560_; lean_object* v_value_2561_; lean_object* v_tail_2562_; uint8_t v___x_2563_; 
v_key_2560_ = lean_ctor_get(v_x_2558_, 0);
v_value_2561_ = lean_ctor_get(v_x_2558_, 1);
v_tail_2562_ = lean_ctor_get(v_x_2558_, 2);
v___x_2563_ = l_Lean_ExprStructEq_beq(v_key_2560_, v_a_2557_);
if (v___x_2563_ == 0)
{
v_x_2558_ = v_tail_2562_;
goto _start;
}
else
{
lean_object* v___x_2565_; 
lean_inc(v_value_2561_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_value_2561_);
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2566_, v_x_2567_);
lean_dec(v_x_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_buckets_2571_; lean_object* v___x_2572_; uint64_t v___x_2573_; uint64_t v___x_2574_; uint64_t v___x_2575_; uint64_t v_fold_2576_; uint64_t v___x_2577_; uint64_t v___x_2578_; uint64_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; size_t v___x_2582_; size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_buckets_2571_ = lean_ctor_get(v_m_2569_, 1);
v___x_2572_ = lean_array_get_size(v_buckets_2571_);
v___x_2573_ = l_Lean_ExprStructEq_hash(v_a_2570_);
v___x_2574_ = 32ULL;
v___x_2575_ = lean_uint64_shift_right(v___x_2573_, v___x_2574_);
v_fold_2576_ = lean_uint64_xor(v___x_2573_, v___x_2575_);
v___x_2577_ = 16ULL;
v___x_2578_ = lean_uint64_shift_right(v_fold_2576_, v___x_2577_);
v___x_2579_ = lean_uint64_xor(v_fold_2576_, v___x_2578_);
v___x_2580_ = lean_uint64_to_usize(v___x_2579_);
v___x_2581_ = lean_usize_of_nat(v___x_2572_);
v___x_2582_ = ((size_t)1ULL);
v___x_2583_ = lean_usize_sub(v___x_2581_, v___x_2582_);
v___x_2584_ = lean_usize_land(v___x_2580_, v___x_2583_);
v___x_2585_ = lean_array_uget_borrowed(v_buckets_2571_, v___x_2584_);
v___x_2586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2570_, v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2587_, v_a_2588_);
lean_dec_ref(v_a_2588_);
lean_dec_ref(v_m_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2590_, lean_object* v___y_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
lean_inc(v___y_2591_);
v___x_2598_ = lean_apply_7(v_k_2590_, v_b_2592_, v___y_2591_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, lean_box(0));
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2599_, lean_object* v___y_2600_, lean_object* v_b_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2599_, v___y_2600_, v_b_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2600_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2608_, uint8_t v_bi_2609_, lean_object* v_type_2610_, lean_object* v_k_2611_, uint8_t v_kind_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___f_2619_; lean_object* v___x_2620_; 
lean_inc(v___y_2613_);
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2619_, 0, v_k_2611_);
lean_closure_set(v___f_2619_, 1, v___y_2613_);
v___x_2620_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2608_, v_bi_2609_, v_type_2610_, v___f_2619_, v_kind_2612_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2620_) == 0)
{
return v___x_2620_;
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2629_, lean_object* v_bi_2630_, lean_object* v_type_2631_, lean_object* v_k_2632_, lean_object* v_kind_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
uint8_t v_bi_boxed_2640_; uint8_t v_kind_boxed_2641_; lean_object* v_res_2642_; 
v_bi_boxed_2640_ = lean_unbox(v_bi_2630_);
v_kind_boxed_2641_ = lean_unbox(v_kind_2633_);
v_res_2642_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2629_, v_bi_boxed_2640_, v_type_2631_, v_k_2632_, v_kind_boxed_2641_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2643_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2657_, lean_object* v_type_2658_, lean_object* v_val_2659_, lean_object* v_k_2660_, uint8_t v_nondep_2661_, uint8_t v_kind_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___f_2669_; lean_object* v___x_2670_; 
lean_inc(v___y_2663_);
v___f_2669_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2669_, 0, v_k_2660_);
lean_closure_set(v___f_2669_, 1, v___y_2663_);
v___x_2670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2657_, v_type_2658_, v_val_2659_, v___f_2669_, v_nondep_2661_, v_kind_2662_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2670_) == 0)
{
return v___x_2670_;
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2679_, lean_object* v_type_2680_, lean_object* v_val_2681_, lean_object* v_k_2682_, lean_object* v_nondep_2683_, lean_object* v_kind_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_nondep_boxed_2691_; uint8_t v_kind_boxed_2692_; lean_object* v_res_2693_; 
v_nondep_boxed_2691_ = lean_unbox(v_nondep_2683_);
v_kind_boxed_2692_ = lean_unbox(v_kind_2684_);
v_res_2693_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2679_, v_type_2680_, v_val_2681_, v_k_2682_, v_nondep_boxed_2691_, v_kind_boxed_2692_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2693_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = l_Lean_maxRecDepthErrorMessage;
v___x_2700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2702_ = l_Lean_MessageData_ofFormat(v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2704_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2705_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2706_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_ref_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___y_2722_; lean_object* v_toCold_2731_; lean_object* v_currRecDepth_2732_; lean_object* v_ref_2733_; uint16_t v_optionFlags_2734_; uint8_t v_suppressElabErrors_2735_; uint8_t v_checkDeprecated_2736_; uint8_t v_isRecordingDeps_2737_; lean_object* v_maxRecDepth_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_toCold_2731_ = lean_ctor_get(v___y_2718_, 0);
v_currRecDepth_2732_ = lean_ctor_get(v___y_2718_, 1);
v_ref_2733_ = lean_ctor_get(v___y_2718_, 2);
v_optionFlags_2734_ = lean_ctor_get_uint16(v___y_2718_, sizeof(void*)*3);
v_suppressElabErrors_2735_ = lean_ctor_get_uint8(v___y_2718_, sizeof(void*)*3 + 2);
v_checkDeprecated_2736_ = lean_ctor_get_uint8(v___y_2718_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2737_ = lean_ctor_get_uint8(v___y_2718_, sizeof(void*)*3 + 4);
v_maxRecDepth_2743_ = lean_ctor_get(v_toCold_2731_, 3);
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = lean_nat_dec_eq(v_maxRecDepth_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_nat_dec_eq(v_currRecDepth_2732_, v_maxRecDepth_2743_);
if (v___x_2746_ == 0)
{
goto v___jp_2738_;
}
else
{
lean_object* v___x_2747_; 
lean_dec_ref(v_x_2714_);
lean_inc(v_ref_2733_);
v___x_2747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2733_);
v___y_2722_ = v___x_2747_;
goto v___jp_2721_;
}
}
else
{
goto v___jp_2738_;
}
v___jp_2721_:
{
if (lean_obj_tag(v___y_2722_) == 0)
{
return v___y_2722_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___y_2722_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___y_2722_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___y_2722_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___y_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
v___jp_2738_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_add(v_currRecDepth_2732_, v___x_2739_);
lean_inc(v_ref_2733_);
lean_inc_ref(v_toCold_2731_);
v___x_2741_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2741_, 0, v_toCold_2731_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
lean_ctor_set(v___x_2741_, 2, v_ref_2733_);
lean_ctor_set_uint16(v___x_2741_, sizeof(void*)*3, v_optionFlags_2734_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*3 + 2, v_suppressElabErrors_2735_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*3 + 3, v_checkDeprecated_2736_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*3 + 4, v_isRecordingDeps_2737_);
lean_inc(v___y_2719_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2716_);
lean_inc(v___y_2715_);
v___x_2742_ = lean_apply_6(v_x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___x_2741_, v___y_2719_, lean_box(0));
v___y_2722_ = v___x_2742_;
goto v___jp_2721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2756_, lean_object* v_pre_2757_, lean_object* v_post_2758_, lean_object* v_usedLetOnly_2759_, lean_object* v_skipConstInApp_2760_, lean_object* v_skipInstances_2761_, lean_object* v_body_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v_usedLetOnly_boxed_2770_; uint8_t v_skipConstInApp_boxed_2771_; uint8_t v_skipInstances_boxed_2772_; lean_object* v_res_2773_; 
v_usedLetOnly_boxed_2770_ = lean_unbox(v_usedLetOnly_2759_);
v_skipConstInApp_boxed_2771_ = lean_unbox(v_skipConstInApp_2760_);
v_skipInstances_boxed_2772_ = lean_unbox(v_skipInstances_2761_);
v_res_2773_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2756_, v_pre_2757_, v_post_2758_, v_usedLetOnly_boxed_2770_, v_skipConstInApp_boxed_2771_, v_skipInstances_boxed_2772_, v_body_2762_, v_x_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
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
lean_dec_ref_known(v_a_2824_, 1);
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
lean_dec_ref_known(v_a_2824_, 1);
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
lean_dec_ref_known(v_a_2824_, 1);
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
lean_dec_ref_known(v_e_x3f_2834_, 1);
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
lean_object* v_binderName_2864_; lean_object* v_binderType_2865_; lean_object* v_body_2866_; uint8_t v_binderInfo_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___f_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_binderName_2864_ = lean_ctor_get(v_e_2857_, 0);
lean_inc(v_binderName_2864_);
v_binderType_2865_ = lean_ctor_get(v_e_2857_, 1);
lean_inc_ref(v_binderType_2865_);
v_body_2866_ = lean_ctor_get(v_e_2857_, 2);
lean_inc_ref(v_body_2866_);
v_binderInfo_2867_ = lean_ctor_get_uint8(v_e_2857_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2857_, 3);
v___x_2868_ = lean_box(v_usedLetOnly_2853_);
v___x_2869_ = lean_box(v_skipConstInApp_2854_);
v___x_2870_ = lean_box(v_skipInstances_2855_);
lean_inc_ref(v_post_2852_);
lean_inc_ref(v_pre_2851_);
lean_inc_ref(v_fvars_2856_);
v___f_2871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2871_, 0, v_fvars_2856_);
lean_closure_set(v___f_2871_, 1, v_pre_2851_);
lean_closure_set(v___f_2871_, 2, v_post_2852_);
lean_closure_set(v___f_2871_, 3, v___x_2868_);
lean_closure_set(v___f_2871_, 4, v___x_2869_);
lean_closure_set(v___f_2871_, 5, v___x_2870_);
lean_closure_set(v___f_2871_, 6, v_body_2866_);
v___x_2872_ = lean_expr_instantiate_rev(v_binderType_2865_, v_fvars_2856_);
lean_dec_ref(v_fvars_2856_);
lean_dec_ref(v_binderType_2865_);
v___x_2873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2851_, v_post_2852_, v_usedLetOnly_2853_, v_skipConstInApp_2854_, v_skipInstances_2855_, v___x_2872_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = 0;
v___x_2876_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2864_, v_binderInfo_2867_, v_a_2874_, v___f_2871_, v___x_2875_, v_a_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
return v___x_2876_;
}
else
{
lean_dec_ref(v___f_2871_);
lean_dec(v_binderName_2864_);
return v___x_2873_;
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
lean_dec_ref_known(v___x_2878_, 1);
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
lean_dec_ref_known(v___x_2883_, 1);
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
lean_object* v_declName_2933_; lean_object* v_type_2934_; lean_object* v_value_2935_; lean_object* v_body_2936_; uint8_t v_nondep_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_declName_2933_ = lean_ctor_get(v_e_2926_, 0);
lean_inc(v_declName_2933_);
v_type_2934_ = lean_ctor_get(v_e_2926_, 1);
lean_inc_ref(v_type_2934_);
v_value_2935_ = lean_ctor_get(v_e_2926_, 2);
lean_inc_ref(v_value_2935_);
v_body_2936_ = lean_ctor_get(v_e_2926_, 3);
lean_inc_ref(v_body_2936_);
v_nondep_2937_ = lean_ctor_get_uint8(v_e_2926_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2926_, 4);
v___x_2938_ = lean_box(v_usedLetOnly_2922_);
v___x_2939_ = lean_box(v_skipConstInApp_2923_);
v___x_2940_ = lean_box(v_skipInstances_2924_);
lean_inc_ref_n(v_post_2921_, 2);
lean_inc_ref_n(v_pre_2920_, 2);
lean_inc_ref(v_fvars_2925_);
v___f_2941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2941_, 0, v_fvars_2925_);
lean_closure_set(v___f_2941_, 1, v_pre_2920_);
lean_closure_set(v___f_2941_, 2, v_post_2921_);
lean_closure_set(v___f_2941_, 3, v___x_2938_);
lean_closure_set(v___f_2941_, 4, v___x_2939_);
lean_closure_set(v___f_2941_, 5, v___x_2940_);
lean_closure_set(v___f_2941_, 6, v_body_2936_);
v___x_2942_ = lean_expr_instantiate_rev(v_type_2934_, v_fvars_2925_);
lean_dec_ref(v_type_2934_);
v___x_2943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v___x_2942_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = lean_expr_instantiate_rev(v_value_2935_, v_fvars_2925_);
lean_dec_ref(v_fvars_2925_);
lean_dec_ref(v_value_2935_);
v___x_2946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2920_, v_post_2921_, v_usedLetOnly_2922_, v_skipConstInApp_2923_, v_skipInstances_2924_, v___x_2945_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2933_, v_a_2944_, v_a_2947_, v___f_2941_, v_nondep_2937_, v___x_2948_, v_a_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2949_;
}
else
{
lean_dec(v_a_2944_);
lean_dec_ref(v___f_2941_);
lean_dec(v_declName_2933_);
return v___x_2946_;
}
}
else
{
lean_dec_ref(v___f_2941_);
lean_dec_ref(v_value_2935_);
lean_dec(v_declName_2933_);
lean_dec_ref(v_fvars_2925_);
lean_dec_ref(v_post_2921_);
lean_dec_ref(v_pre_2920_);
return v___x_2943_;
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
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = 0;
v___x_2954_ = 1;
v___x_2955_ = l_Lean_Meta_mkLetFVars(v_fvars_2925_, v_a_2952_, v_usedLetOnly_2922_, v___x_2953_, v___x_2954_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec_ref(v_fvars_2925_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
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
lean_object* v_v_2974_; lean_object* v___x_2975_; lean_object* v_bs_x27_2976_; lean_object* v___x_2977_; 
v_v_2974_ = lean_array_uget(v_bs_2965_, v_i_2964_);
v___x_2975_ = lean_unsigned_to_nat(0u);
v_bs_x27_2976_ = lean_array_uset(v_bs_2965_, v_i_2964_, v___x_2975_);
lean_inc_ref(v_post_2959_);
lean_inc_ref(v_pre_2958_);
v___x_2977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2958_, v_post_2959_, v_usedLetOnly_2960_, v_skipConstInApp_2961_, v_skipInstances_2962_, v_v_2974_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; size_t v___x_2979_; size_t v___x_2980_; lean_object* v___x_2981_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_add(v_i_2964_, v___x_2979_);
v___x_2981_ = lean_array_uset(v_bs_x27_2976_, v_i_2964_, v_a_2978_);
v_i_2964_ = v___x_2980_;
v_bs_2965_ = v___x_2981_;
goto _start;
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_bs_x27_2976_);
lean_dec_ref(v_post_2959_);
lean_dec_ref(v_pre_2958_);
v_a_2983_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2977_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2977_);
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
lean_dec_ref_known(v_a_3060_, 1);
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
lean_dec_ref_known(v_a_3060_, 1);
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
lean_dec_ref_known(v_x_3103_, 2);
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
lean_dec_ref_known(v___x_3121_, 1);
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
lean_dec_ref_known(v___x_3134_, 1);
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
lean_dec_ref_known(v___x_3138_, 1);
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
lean_dec_ref_known(v___x_3159_, 1);
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
lean_dec_ref_known(v___x_3181_, 1);
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
lean_dec_ref_known(v_a_3183_, 1);
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
lean_dec_ref_known(v_a_3183_, 1);
v___x_3228_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3169_, v_post_3171_, v_usedLetOnly_3172_, v_skipConstInApp_3173_, v_skipInstances_3174_, v_e_3227_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3228_;
}
default: 
{
lean_object* v_e_x3f_3229_; 
lean_del_object(v___x_3185_);
v_e_x3f_3229_ = lean_ctor_get(v_a_3183_, 0);
lean_inc(v_e_x3f_3229_);
lean_dec_ref_known(v_a_3183_, 1);
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
lean_dec_ref_known(v_e_x3f_3229_, 1);
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
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = lean_ptr_addr(v_expr_3202_);
v___x_3206_ = lean_ptr_addr(v_a_3204_);
v___x_3207_ = lean_usize_dec_eq(v___x_3205_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_inc(v_data_3201_);
lean_dec_ref_known(v___y_3188_, 2);
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
lean_dec_ref_known(v___y_3188_, 2);
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
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = lean_ptr_addr(v_struct_3213_);
v___x_3217_ = lean_ptr_addr(v_a_3215_);
v___x_3218_ = lean_usize_dec_eq(v___x_3216_, v___x_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
lean_inc(v_idx_3212_);
lean_inc(v_typeName_3211_);
lean_dec_ref_known(v___y_3188_, 3);
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
lean_dec_ref_known(v___y_3188_, 3);
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
lean_dec_ref_known(v___x_3289_, 1);
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
lean_dec_ref_known(v___x_3283_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3322_, lean_object* v_post_3323_, uint8_t v_usedLetOnly_3324_, uint8_t v_skipConstInApp_3325_, uint8_t v_skipInstances_3326_, lean_object* v_fvars_3327_, lean_object* v_e_3328_, lean_object* v_a_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
if (lean_obj_tag(v_e_3328_) == 7)
{
lean_object* v_binderName_3335_; lean_object* v_binderType_3336_; lean_object* v_body_3337_; uint8_t v_binderInfo_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_binderName_3335_ = lean_ctor_get(v_e_3328_, 0);
lean_inc(v_binderName_3335_);
v_binderType_3336_ = lean_ctor_get(v_e_3328_, 1);
lean_inc_ref(v_binderType_3336_);
v_body_3337_ = lean_ctor_get(v_e_3328_, 2);
lean_inc_ref(v_body_3337_);
v_binderInfo_3338_ = lean_ctor_get_uint8(v_e_3328_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3328_, 3);
v___x_3339_ = lean_box(v_usedLetOnly_3324_);
v___x_3340_ = lean_box(v_skipConstInApp_3325_);
v___x_3341_ = lean_box(v_skipInstances_3326_);
lean_inc_ref(v_post_3323_);
lean_inc_ref(v_pre_3322_);
lean_inc_ref(v_fvars_3327_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3342_, 0, v_fvars_3327_);
lean_closure_set(v___f_3342_, 1, v_pre_3322_);
lean_closure_set(v___f_3342_, 2, v_post_3323_);
lean_closure_set(v___f_3342_, 3, v___x_3339_);
lean_closure_set(v___f_3342_, 4, v___x_3340_);
lean_closure_set(v___f_3342_, 5, v___x_3341_);
lean_closure_set(v___f_3342_, 6, v_body_3337_);
v___x_3343_ = lean_expr_instantiate_rev(v_binderType_3336_, v_fvars_3327_);
lean_dec_ref(v_fvars_3327_);
lean_dec_ref(v_binderType_3336_);
v___x_3344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3322_, v_post_3323_, v_usedLetOnly_3324_, v_skipConstInApp_3325_, v_skipInstances_3326_, v___x_3343_, v_a_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; uint8_t v___x_3346_; lean_object* v___x_3347_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = 0;
v___x_3347_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3335_, v_binderInfo_3338_, v_a_3345_, v___f_3342_, v___x_3346_, v_a_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3347_;
}
else
{
lean_dec_ref(v___f_3342_);
lean_dec(v_binderName_3335_);
return v___x_3344_;
}
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_expr_instantiate_rev(v_e_3328_, v_fvars_3327_);
lean_dec_ref(v_e_3328_);
lean_inc_ref(v_post_3323_);
lean_inc_ref(v_pre_3322_);
v___x_3349_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3322_, v_post_3323_, v_usedLetOnly_3324_, v_skipConstInApp_3325_, v_skipInstances_3326_, v___x_3348_, v_a_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; uint8_t v___x_3351_; uint8_t v___x_3352_; uint8_t v___x_3353_; lean_object* v___x_3354_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v___x_3351_ = 0;
v___x_3352_ = 1;
v___x_3353_ = 1;
v___x_3354_ = l_Lean_Meta_mkForallFVars(v_fvars_3327_, v_a_3350_, v___x_3351_, v_usedLetOnly_3324_, v___x_3352_, v___x_3353_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec_ref(v_fvars_3327_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3322_, v_post_3323_, v_usedLetOnly_3324_, v_skipConstInApp_3325_, v_skipInstances_3326_, v_a_3355_, v_a_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3356_;
}
else
{
lean_dec_ref(v_post_3323_);
lean_dec_ref(v_pre_3322_);
return v___x_3354_;
}
}
else
{
lean_dec_ref(v_fvars_3327_);
lean_dec_ref(v_post_3323_);
lean_dec_ref(v_pre_3322_);
return v___x_3349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3357_, lean_object* v_pre_3358_, lean_object* v_post_3359_, uint8_t v_usedLetOnly_3360_, uint8_t v_skipConstInApp_3361_, uint8_t v_skipInstances_3362_, lean_object* v_body_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_array_push(v_fvars_3357_, v_x_3364_);
v___x_3372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3358_, v_post_3359_, v_usedLetOnly_3360_, v_skipConstInApp_3361_, v_skipInstances_3362_, v___x_3371_, v_body_3363_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3373_, lean_object* v_post_3374_, lean_object* v_usedLetOnly_3375_, lean_object* v_skipConstInApp_3376_, lean_object* v_skipInstances_3377_, lean_object* v_e_3378_, lean_object* v_a_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v_usedLetOnly_boxed_3385_; uint8_t v_skipConstInApp_boxed_3386_; uint8_t v_skipInstances_boxed_3387_; lean_object* v_res_3388_; 
v_usedLetOnly_boxed_3385_ = lean_unbox(v_usedLetOnly_3375_);
v_skipConstInApp_boxed_3386_ = lean_unbox(v_skipConstInApp_3376_);
v_skipInstances_boxed_3387_ = lean_unbox(v_skipInstances_3377_);
v_res_3388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3373_, v_post_3374_, v_usedLetOnly_boxed_3385_, v_skipConstInApp_boxed_3386_, v_skipInstances_boxed_3387_, v_e_3378_, v_a_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v_a_3379_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3389_, lean_object* v_post_3390_, lean_object* v_usedLetOnly_3391_, lean_object* v_skipConstInApp_3392_, lean_object* v_skipInstances_3393_, lean_object* v_sz_3394_, lean_object* v_i_3395_, lean_object* v_bs_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v_usedLetOnly_boxed_3403_; uint8_t v_skipConstInApp_boxed_3404_; uint8_t v_skipInstances_boxed_3405_; size_t v_sz_boxed_3406_; size_t v_i_boxed_3407_; lean_object* v_res_3408_; 
v_usedLetOnly_boxed_3403_ = lean_unbox(v_usedLetOnly_3391_);
v_skipConstInApp_boxed_3404_ = lean_unbox(v_skipConstInApp_3392_);
v_skipInstances_boxed_3405_ = lean_unbox(v_skipInstances_3393_);
v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3394_);
lean_dec(v_sz_3394_);
v_i_boxed_3407_ = lean_unbox_usize(v_i_3395_);
lean_dec(v_i_3395_);
v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3389_, v_post_3390_, v_usedLetOnly_boxed_3403_, v_skipConstInApp_boxed_3404_, v_skipInstances_boxed_3405_, v_sz_boxed_3406_, v_i_boxed_3407_, v_bs_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3409_, lean_object* v_post_3410_, lean_object* v_usedLetOnly_3411_, lean_object* v_skipConstInApp_3412_, lean_object* v_skipInstances_3413_, lean_object* v_e_3414_, lean_object* v_a_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v_usedLetOnly_boxed_3421_; uint8_t v_skipConstInApp_boxed_3422_; uint8_t v_skipInstances_boxed_3423_; lean_object* v_res_3424_; 
v_usedLetOnly_boxed_3421_ = lean_unbox(v_usedLetOnly_3411_);
v_skipConstInApp_boxed_3422_ = lean_unbox(v_skipConstInApp_3412_);
v_skipInstances_boxed_3423_ = lean_unbox(v_skipInstances_3413_);
v_res_3424_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3409_, v_post_3410_, v_usedLetOnly_boxed_3421_, v_skipConstInApp_boxed_3422_, v_skipInstances_boxed_3423_, v_e_3414_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v_a_3415_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3425_, lean_object* v_post_3426_, lean_object* v_usedLetOnly_3427_, lean_object* v_skipConstInApp_3428_, lean_object* v_skipInstances_3429_, lean_object* v_fvars_3430_, lean_object* v_e_3431_, lean_object* v_a_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v_usedLetOnly_boxed_3438_; uint8_t v_skipConstInApp_boxed_3439_; uint8_t v_skipInstances_boxed_3440_; lean_object* v_res_3441_; 
v_usedLetOnly_boxed_3438_ = lean_unbox(v_usedLetOnly_3427_);
v_skipConstInApp_boxed_3439_ = lean_unbox(v_skipConstInApp_3428_);
v_skipInstances_boxed_3440_ = lean_unbox(v_skipInstances_3429_);
v_res_3441_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3425_, v_post_3426_, v_usedLetOnly_boxed_3438_, v_skipConstInApp_boxed_3439_, v_skipInstances_boxed_3440_, v_fvars_3430_, v_e_3431_, v_a_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v_a_3432_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3442_, lean_object* v_post_3443_, lean_object* v_usedLetOnly_3444_, lean_object* v_skipConstInApp_3445_, lean_object* v_skipInstances_3446_, lean_object* v_fvars_3447_, lean_object* v_e_3448_, lean_object* v_a_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_usedLetOnly_boxed_3455_; uint8_t v_skipConstInApp_boxed_3456_; uint8_t v_skipInstances_boxed_3457_; lean_object* v_res_3458_; 
v_usedLetOnly_boxed_3455_ = lean_unbox(v_usedLetOnly_3444_);
v_skipConstInApp_boxed_3456_ = lean_unbox(v_skipConstInApp_3445_);
v_skipInstances_boxed_3457_ = lean_unbox(v_skipInstances_3446_);
v_res_3458_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3442_, v_post_3443_, v_usedLetOnly_boxed_3455_, v_skipConstInApp_boxed_3456_, v_skipInstances_boxed_3457_, v_fvars_3447_, v_e_3448_, v_a_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v_a_3449_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3459_, lean_object* v_post_3460_, lean_object* v_usedLetOnly_3461_, lean_object* v_skipConstInApp_3462_, lean_object* v_skipInstances_3463_, lean_object* v_fvars_3464_, lean_object* v_e_3465_, lean_object* v_a_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
uint8_t v_usedLetOnly_boxed_3472_; uint8_t v_skipConstInApp_boxed_3473_; uint8_t v_skipInstances_boxed_3474_; lean_object* v_res_3475_; 
v_usedLetOnly_boxed_3472_ = lean_unbox(v_usedLetOnly_3461_);
v_skipConstInApp_boxed_3473_ = lean_unbox(v_skipConstInApp_3462_);
v_skipInstances_boxed_3474_ = lean_unbox(v_skipInstances_3463_);
v_res_3475_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3459_, v_post_3460_, v_usedLetOnly_boxed_3472_, v_skipConstInApp_boxed_3473_, v_skipInstances_boxed_3474_, v_fvars_3464_, v_e_3465_, v_a_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v_a_3466_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3476_, lean_object* v___x_3477_, lean_object* v_pre_3478_, lean_object* v_post_3479_, lean_object* v_usedLetOnly_3480_, lean_object* v_skipConstInApp_3481_, lean_object* v_skipInstances_3482_, lean_object* v_a_3483_, lean_object* v_b_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
uint8_t v_usedLetOnly_boxed_3491_; uint8_t v_skipConstInApp_boxed_3492_; uint8_t v_skipInstances_boxed_3493_; lean_object* v_res_3494_; 
v_usedLetOnly_boxed_3491_ = lean_unbox(v_usedLetOnly_3480_);
v_skipConstInApp_boxed_3492_ = lean_unbox(v_skipConstInApp_3481_);
v_skipInstances_boxed_3493_ = lean_unbox(v_skipInstances_3482_);
v_res_3494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3476_, v___x_3477_, v_pre_3478_, v_post_3479_, v_usedLetOnly_boxed_3491_, v_skipConstInApp_boxed_3492_, v_skipInstances_boxed_3493_, v_a_3483_, v_b_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___x_3477_);
lean_dec(v_upperBound_3476_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3495_, lean_object* v_pre_3496_, lean_object* v_post_3497_, lean_object* v_usedLetOnly_3498_, lean_object* v_skipConstInApp_3499_, lean_object* v_x_3500_, lean_object* v_x_3501_, lean_object* v_x_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
uint8_t v_skipInstances_boxed_3509_; uint8_t v_usedLetOnly_boxed_3510_; uint8_t v_skipConstInApp_boxed_3511_; lean_object* v_res_3512_; 
v_skipInstances_boxed_3509_ = lean_unbox(v_skipInstances_3495_);
v_usedLetOnly_boxed_3510_ = lean_unbox(v_usedLetOnly_3498_);
v_skipConstInApp_boxed_3511_ = lean_unbox(v_skipConstInApp_3499_);
v_res_3512_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3509_, v_pre_3496_, v_post_3497_, v_usedLetOnly_boxed_3510_, v_skipConstInApp_boxed_3511_, v_x_3500_, v_x_3501_, v_x_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
return v_res_3512_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_unsigned_to_nat(16u);
v___x_3515_ = lean_mk_array(v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3517_ = lean_unsigned_to_nat(0u);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3520_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3520_, 0, lean_box(0));
lean_closure_set(v___x_3520_, 1, lean_box(0));
lean_closure_set(v___x_3520_, 2, v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3521_, lean_object* v_pre_3522_, lean_object* v_post_3523_, uint8_t v_usedLetOnly_3524_, uint8_t v_skipConstInApp_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
uint8_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v_a_3534_; lean_object* v___x_3535_; 
v___x_3531_ = 0;
v___x_3532_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3533_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3532_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3533_);
v___x_3535_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3522_, v_post_3523_, v_usedLetOnly_3524_, v_skipConstInApp_3525_, v___x_3531_, v_input_3521_, v_a_3534_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___x_3537_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3537_, 0, lean_box(0));
lean_closure_set(v___x_3537_, 1, lean_box(0));
lean_closure_set(v___x_3537_, 2, v_a_3534_);
v___x_3538_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3537_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v___x_3538_, 0);
lean_dec(v_unused_3546_);
v___x_3540_ = v___x_3538_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v___x_3538_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 0, v_a_3536_);
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3536_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_dec(v_a_3534_);
return v___x_3535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3547_, lean_object* v_pre_3548_, lean_object* v_post_3549_, lean_object* v_usedLetOnly_3550_, lean_object* v_skipConstInApp_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v_usedLetOnly_boxed_3557_; uint8_t v_skipConstInApp_boxed_3558_; lean_object* v_res_3559_; 
v_usedLetOnly_boxed_3557_ = lean_unbox(v_usedLetOnly_3550_);
v_skipConstInApp_boxed_3558_ = lean_unbox(v_skipConstInApp_3551_);
v_res_3559_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3547_, v_pre_3548_, v_post_3549_, v_usedLetOnly_boxed_3557_, v_skipConstInApp_boxed_3558_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3561_, lean_object* v_p_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v___f_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; lean_object* v_a_3571_; uint8_t v___x_3572_; lean_object* v___x_3573_; 
v___f_3568_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3569_, 0, v_p_3562_);
v___x_3570_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3561_, v_a_3564_);
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = 0;
v___x_3573_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3571_, v___f_3568_, v___f_3569_, v___x_3572_, v___x_3572_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3574_, lean_object* v_p_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Meta_etaStructReduce(v_e_3574_, v_p_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3582_, lean_object* v___x_3583_, lean_object* v_pre_3584_, lean_object* v_post_3585_, uint8_t v_usedLetOnly_3586_, uint8_t v_skipConstInApp_3587_, uint8_t v_skipInstances_3588_, lean_object* v___x_3589_, lean_object* v_inst_3590_, lean_object* v_R_3591_, lean_object* v_a_3592_, lean_object* v_b_3593_, lean_object* v_c_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3582_, v___x_3583_, v_pre_3584_, v_post_3585_, v_usedLetOnly_3586_, v_skipConstInApp_3587_, v_skipInstances_3588_, v_a_3592_, v_b_3593_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3602_ = _args[0];
lean_object* v___x_3603_ = _args[1];
lean_object* v_pre_3604_ = _args[2];
lean_object* v_post_3605_ = _args[3];
lean_object* v_usedLetOnly_3606_ = _args[4];
lean_object* v_skipConstInApp_3607_ = _args[5];
lean_object* v_skipInstances_3608_ = _args[6];
lean_object* v___x_3609_ = _args[7];
lean_object* v_inst_3610_ = _args[8];
lean_object* v_R_3611_ = _args[9];
lean_object* v_a_3612_ = _args[10];
lean_object* v_b_3613_ = _args[11];
lean_object* v_c_3614_ = _args[12];
lean_object* v___y_3615_ = _args[13];
lean_object* v___y_3616_ = _args[14];
lean_object* v___y_3617_ = _args[15];
lean_object* v___y_3618_ = _args[16];
lean_object* v___y_3619_ = _args[17];
lean_object* v___y_3620_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3621_; uint8_t v_skipConstInApp_boxed_3622_; uint8_t v_skipInstances_boxed_3623_; lean_object* v_res_3624_; 
v_usedLetOnly_boxed_3621_ = lean_unbox(v_usedLetOnly_3606_);
v_skipConstInApp_boxed_3622_ = lean_unbox(v_skipConstInApp_3607_);
v_skipInstances_boxed_3623_ = lean_unbox(v_skipInstances_3608_);
v_res_3624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3602_, v___x_3603_, v_pre_3604_, v_post_3605_, v_usedLetOnly_boxed_3621_, v_skipConstInApp_boxed_3622_, v_skipInstances_boxed_3623_, v___x_3609_, v_inst_3610_, v_R_3611_, v_a_3612_, v_b_3613_, v_c_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec(v___x_3609_);
lean_dec_ref(v___x_3603_);
lean_dec(v_upperBound_3602_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3625_, lean_object* v_m_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3626_, v_a_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3629_, lean_object* v_m_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3629_, v_m_3630_, v_a_3631_);
lean_dec_ref(v_a_3631_);
lean_dec_ref(v_m_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3633_, lean_object* v_name_3634_, uint8_t v_bi_3635_, lean_object* v_type_3636_, lean_object* v_k_3637_, uint8_t v_kind_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3634_, v_bi_3635_, v_type_3636_, v_k_3637_, v_kind_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3646_, lean_object* v_name_3647_, lean_object* v_bi_3648_, lean_object* v_type_3649_, lean_object* v_k_3650_, lean_object* v_kind_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v_bi_boxed_3658_; uint8_t v_kind_boxed_3659_; lean_object* v_res_3660_; 
v_bi_boxed_3658_ = lean_unbox(v_bi_3648_);
v_kind_boxed_3659_ = lean_unbox(v_kind_3651_);
v_res_3660_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3646_, v_name_3647_, v_bi_boxed_3658_, v_type_3649_, v_k_3650_, v_kind_boxed_3659_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3661_, lean_object* v_name_3662_, lean_object* v_type_3663_, lean_object* v_val_3664_, lean_object* v_k_3665_, uint8_t v_nondep_3666_, uint8_t v_kind_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3662_, v_type_3663_, v_val_3664_, v_k_3665_, v_nondep_3666_, v_kind_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3675_, lean_object* v_name_3676_, lean_object* v_type_3677_, lean_object* v_val_3678_, lean_object* v_k_3679_, lean_object* v_nondep_3680_, lean_object* v_kind_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v_nondep_boxed_3688_; uint8_t v_kind_boxed_3689_; lean_object* v_res_3690_; 
v_nondep_boxed_3688_ = lean_unbox(v_nondep_3680_);
v_kind_boxed_3689_ = lean_unbox(v_kind_3681_);
v_res_3690_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3675_, v_name_3676_, v_type_3677_, v_val_3678_, v_k_3679_, v_nondep_boxed_3688_, v_kind_boxed_3689_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3691_, lean_object* v_ref_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3692_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3699_, lean_object* v_ref_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3699_, v_ref_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3707_, lean_object* v_x_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3716_, v_x_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3725_, lean_object* v_m_3726_, lean_object* v_a_3727_, lean_object* v_b_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3726_, v_a_3727_, v_b_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3730_, lean_object* v_a_3731_, lean_object* v_x_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3731_, v_x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3734_, lean_object* v_a_3735_, lean_object* v_x_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3734_, v_a_3735_, v_x_3736_);
lean_dec(v_x_3736_);
lean_dec_ref(v_a_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3738_, lean_object* v_a_3739_, lean_object* v_x_3740_){
_start:
{
uint8_t v___x_3741_; 
v___x_3741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3739_, v_x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3742_, lean_object* v_a_3743_, lean_object* v_x_3744_){
_start:
{
uint8_t v_res_3745_; lean_object* v_r_3746_; 
v_res_3745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3742_, v_a_3743_, v_x_3744_);
lean_dec(v_x_3744_);
lean_dec_ref(v_a_3743_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3747_, lean_object* v_data_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3750_, lean_object* v_a_3751_, lean_object* v_b_3752_, lean_object* v_x_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3751_, v_b_3752_, v_x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3755_, lean_object* v_i_3756_, lean_object* v_source_3757_, lean_object* v_target_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3756_, v_source_3757_, v_target_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3761_, v_x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3764_, lean_object* v_inst_3765_, lean_object* v_toBind_3766_, lean_object* v___f_3767_, lean_object* v_____do__lift_3768_){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3769_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3769_, 0, v_____do__lift_3768_);
lean_closure_set(v___x_3769_, 1, v_binderType_3764_);
v___x_3770_ = lean_apply_2(v_inst_3765_, lean_box(0), v___x_3769_);
v___x_3771_ = lean_apply_4(v_toBind_3766_, lean_box(0), lean_box(0), v___x_3770_, v___f_3767_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3772_, lean_object* v_usedFields_3773_, lean_object* v_binderName_3774_, lean_object* v_body_3775_, lean_object* v_val_3776_, lean_object* v_inst_3777_, lean_object* v_inst_3778_, lean_object* v_fieldVal_x3f_3779_, lean_object* v_____do__lift_3780_){
_start:
{
uint8_t v_____do__lift_285__boxed_3781_; lean_object* v_res_3782_; 
v_____do__lift_285__boxed_3781_ = lean_unbox(v_____do__lift_3780_);
v_res_3782_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3772_, v_usedFields_3773_, v_binderName_3774_, v_body_3775_, v_val_3776_, v_inst_3777_, v_inst_3778_, v_fieldVal_x3f_3779_, v_____do__lift_285__boxed_3781_);
lean_dec_ref(v_val_3776_);
lean_dec_ref(v_body_3775_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3783_, lean_object* v_usedFields_3784_, lean_object* v_binderName_3785_, lean_object* v_body_3786_, lean_object* v_inst_3787_, lean_object* v_inst_3788_, lean_object* v_fieldVal_x3f_3789_, lean_object* v_binderType_3790_, lean_object* v_toBind_3791_, lean_object* v_____x_3792_){
_start:
{
if (lean_obj_tag(v_____x_3792_) == 1)
{
lean_object* v_val_3793_; lean_object* v___f_3794_; lean_object* v___f_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_val_3793_ = lean_ctor_get(v_____x_3792_, 0);
lean_inc_n(v_val_3793_, 2);
lean_dec_ref_known(v_____x_3792_, 1);
lean_inc_n(v_inst_3788_, 2);
v___f_3794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3794_, 0, v_toPure_3783_);
lean_closure_set(v___f_3794_, 1, v_usedFields_3784_);
lean_closure_set(v___f_3794_, 2, v_binderName_3785_);
lean_closure_set(v___f_3794_, 3, v_body_3786_);
lean_closure_set(v___f_3794_, 4, v_val_3793_);
lean_closure_set(v___f_3794_, 5, v_inst_3787_);
lean_closure_set(v___f_3794_, 6, v_inst_3788_);
lean_closure_set(v___f_3794_, 7, v_fieldVal_x3f_3789_);
lean_inc(v_toBind_3791_);
v___f_3795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3795_, 0, v_binderType_3790_);
lean_closure_set(v___f_3795_, 1, v_inst_3788_);
lean_closure_set(v___f_3795_, 2, v_toBind_3791_);
lean_closure_set(v___f_3795_, 3, v___f_3794_);
v___x_3796_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3796_, 0, v_val_3793_);
v___x_3797_ = lean_apply_2(v_inst_3788_, lean_box(0), v___x_3796_);
v___x_3798_ = lean_apply_4(v_toBind_3791_, lean_box(0), lean_box(0), v___x_3797_, v___f_3795_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
lean_dec(v_____x_3792_);
lean_dec(v_toBind_3791_);
lean_dec_ref(v_binderType_3790_);
lean_dec(v_fieldVal_x3f_3789_);
lean_dec(v_inst_3788_);
lean_dec_ref(v_inst_3787_);
lean_dec_ref(v_body_3786_);
lean_dec(v_binderName_3785_);
lean_dec(v_usedFields_3784_);
v___x_3799_ = lean_box(0);
v___x_3800_ = lean_apply_2(v_toPure_3783_, lean_box(0), v___x_3799_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3804_, lean_object* v_inst_3805_, lean_object* v_fieldVal_x3f_3806_, lean_object* v_usedFields_3807_, lean_object* v_e_3808_){
_start:
{
lean_object* v_toApplicative_3809_; lean_object* v_toBind_3810_; lean_object* v_toPure_3811_; 
v_toApplicative_3809_ = lean_ctor_get(v_inst_3804_, 0);
v_toBind_3810_ = lean_ctor_get(v_inst_3804_, 1);
v_toPure_3811_ = lean_ctor_get(v_toApplicative_3809_, 1);
lean_inc(v_toPure_3811_);
if (lean_obj_tag(v_e_3808_) == 6)
{
lean_object* v_binderName_3816_; lean_object* v_binderType_3817_; lean_object* v_body_3818_; lean_object* v___f_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
lean_inc_n(v_toBind_3810_, 2);
v_binderName_3816_ = lean_ctor_get(v_e_3808_, 0);
lean_inc_n(v_binderName_3816_, 2);
v_binderType_3817_ = lean_ctor_get(v_e_3808_, 1);
lean_inc_ref(v_binderType_3817_);
v_body_3818_ = lean_ctor_get(v_e_3808_, 2);
lean_inc_ref(v_body_3818_);
lean_dec_ref_known(v_e_3808_, 3);
lean_inc(v_fieldVal_x3f_3806_);
v___f_3819_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3819_, 0, v_toPure_3811_);
lean_closure_set(v___f_3819_, 1, v_usedFields_3807_);
lean_closure_set(v___f_3819_, 2, v_binderName_3816_);
lean_closure_set(v___f_3819_, 3, v_body_3818_);
lean_closure_set(v___f_3819_, 4, v_inst_3804_);
lean_closure_set(v___f_3819_, 5, v_inst_3805_);
lean_closure_set(v___f_3819_, 6, v_fieldVal_x3f_3806_);
lean_closure_set(v___f_3819_, 7, v_binderType_3817_);
lean_closure_set(v___f_3819_, 8, v_toBind_3810_);
v___x_3820_ = lean_apply_1(v_fieldVal_x3f_3806_, v_binderName_3816_);
v___x_3821_ = lean_apply_4(v_toBind_3810_, lean_box(0), lean_box(0), v___x_3820_, v___f_3819_);
return v___x_3821_;
}
else
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3838_; 
lean_dec(v_fieldVal_x3f_3806_);
lean_dec(v_inst_3805_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_inst_3804_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; lean_object* v_unused_3840_; 
v_unused_3839_ = lean_ctor_get(v_inst_3804_, 1);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_inst_3804_, 0);
lean_dec(v_unused_3840_);
v___x_3823_ = v_inst_3804_;
v_isShared_3824_ = v_isSharedCheck_3838_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v_inst_3804_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3838_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3825_ = l_Lean_Expr_cleanupAnnotations(v_e_3808_);
v___x_3826_ = l_Lean_Expr_isApp(v___x_3825_);
if (v___x_3826_ == 0)
{
lean_dec_ref(v___x_3825_);
lean_del_object(v___x_3823_);
goto v___jp_3812_;
}
else
{
lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3825_);
v___x_3828_ = l_Lean_Expr_isApp(v___x_3827_);
if (v___x_3828_ == 0)
{
lean_dec_ref(v___x_3827_);
lean_dec_ref(v___x_3825_);
lean_del_object(v___x_3823_);
goto v___jp_3812_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3827_);
lean_dec_ref(v___x_3827_);
v___x_3830_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3831_ = l_Lean_Expr_isConstOf(v___x_3829_, v___x_3830_);
lean_dec_ref(v___x_3829_);
if (v___x_3831_ == 0)
{
lean_dec_ref(v___x_3825_);
lean_del_object(v___x_3823_);
goto v___jp_3812_;
}
else
{
lean_object* v_arg_3832_; lean_object* v___x_3834_; 
lean_dec_ref(v_e_3808_);
v_arg_3832_ = lean_ctor_get(v___x_3825_, 1);
lean_inc_ref(v_arg_3832_);
lean_dec_ref(v___x_3825_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 1, v_arg_3832_);
lean_ctor_set(v___x_3823_, 0, v_usedFields_3807_);
v___x_3834_ = v___x_3823_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_usedFields_3807_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v_arg_3832_);
v___x_3834_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
v___x_3836_ = lean_apply_2(v_toPure_3811_, lean_box(0), v___x_3835_);
return v___x_3836_;
}
}
}
}
}
}
v___jp_3812_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v_usedFields_3807_);
lean_ctor_set(v___x_3813_, 1, v_e_3808_);
v___x_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
v___x_3815_ = lean_apply_2(v_toPure_3811_, lean_box(0), v___x_3814_);
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3841_, lean_object* v_usedFields_3842_, lean_object* v_binderName_3843_, lean_object* v_body_3844_, lean_object* v_val_3845_, lean_object* v_inst_3846_, lean_object* v_inst_3847_, lean_object* v_fieldVal_x3f_3848_, uint8_t v_____do__lift_3849_){
_start:
{
if (v_____do__lift_3849_ == 0)
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec(v_fieldVal_x3f_3848_);
lean_dec(v_inst_3847_);
lean_dec_ref(v_inst_3846_);
lean_dec(v_binderName_3843_);
lean_dec(v_usedFields_3842_);
v___x_3850_ = lean_box(0);
v___x_3851_ = lean_apply_2(v_toPure_3841_, lean_box(0), v___x_3850_);
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec(v_toPure_3841_);
v___x_3852_ = l_Lean_NameSet_insert(v_usedFields_3842_, v_binderName_3843_);
v___x_3853_ = lean_expr_instantiate1(v_body_3844_, v_val_3845_);
v___x_3854_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3846_, v_inst_3847_, v_fieldVal_x3f_3848_, v___x_3852_, v___x_3853_);
return v___x_3854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3855_, lean_object* v_inst_3856_, lean_object* v_inst_3857_, lean_object* v_fieldVal_x3f_3858_, lean_object* v_usedFields_3859_, lean_object* v_e_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3856_, v_inst_3857_, v_fieldVal_x3f_3858_, v_usedFields_3859_, v_e_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3862_, lean_object* v_inst_3863_, lean_object* v_fieldVal_x3f_3864_, lean_object* v_toPure_3865_, lean_object* v_____s_3866_){
_start:
{
lean_object* v_fst_3867_; 
v_fst_3867_ = lean_ctor_get(v_____s_3866_, 0);
if (lean_obj_tag(v_fst_3867_) == 0)
{
lean_object* v_snd_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_dec(v_toPure_3865_);
v_snd_3868_ = lean_ctor_get(v_____s_3866_, 1);
lean_inc(v_snd_3868_);
lean_dec_ref(v_____s_3866_);
v___x_3869_ = l_Lean_NameSet_empty;
v___x_3870_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3862_, v_inst_3863_, v_fieldVal_x3f_3864_, v___x_3869_, v_snd_3868_);
return v___x_3870_;
}
else
{
lean_object* v_val_3871_; lean_object* v___x_3872_; 
lean_inc_ref(v_fst_3867_);
lean_dec_ref(v_____s_3866_);
lean_dec(v_fieldVal_x3f_3864_);
lean_dec(v_inst_3863_);
lean_dec_ref(v_inst_3862_);
v_val_3871_ = lean_ctor_get(v_fst_3867_, 0);
lean_inc(v_val_3871_);
lean_dec_ref_known(v_fst_3867_, 1);
v___x_3872_ = lean_apply_2(v_toPure_3865_, lean_box(0), v_val_3871_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3873_, lean_object* v_a_3874_, lean_object* v___x_3875_, lean_object* v_toPure_3876_, lean_object* v_____r_3877_){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3878_ = lean_expr_instantiate1(v_body_3873_, v_a_3874_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3875_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
v___x_3881_ = lean_apply_2(v_toPure_3876_, lean_box(0), v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3882_, lean_object* v_a_3883_, lean_object* v___x_3884_, lean_object* v_toPure_3885_, lean_object* v_____r_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3882_, v_a_3883_, v___x_3884_, v_toPure_3885_, v_____r_3886_);
lean_dec_ref(v_a_3883_);
lean_dec_ref(v_body_3882_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3890_, lean_object* v_toPure_3891_, lean_object* v___f_3892_, uint8_t v_____do__lift_3893_){
_start:
{
if (v_____do__lift_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec(v___f_3892_);
v___x_3894_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
lean_ctor_set(v___x_3895_, 1, v_snd_3890_);
v___x_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
v___x_3897_ = lean_apply_2(v_toPure_3891_, lean_box(0), v___x_3896_);
return v___x_3897_;
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v_toPure_3891_);
lean_dec(v_snd_3890_);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_apply_1(v___f_3892_, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3900_, lean_object* v_toPure_3901_, lean_object* v___f_3902_, lean_object* v_____do__lift_3903_){
_start:
{
uint8_t v_____do__lift_566__boxed_3904_; lean_object* v_res_3905_; 
v_____do__lift_566__boxed_3904_ = lean_unbox(v_____do__lift_3903_);
v_res_3905_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3900_, v_toPure_3901_, v___f_3902_, v_____do__lift_566__boxed_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3906_, lean_object* v_inst_3907_, lean_object* v_toBind_3908_, lean_object* v___f_3909_, lean_object* v_____do__lift_3910_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3911_, 0, v_____do__lift_3910_);
lean_closure_set(v___x_3911_, 1, v_binderType_3906_);
v___x_3912_ = lean_apply_2(v_inst_3907_, lean_box(0), v___x_3911_);
v___x_3913_ = lean_apply_4(v_toBind_3908_, lean_box(0), lean_box(0), v___x_3912_, v___f_3909_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3914_, lean_object* v_toPure_3915_, lean_object* v_levels_x3f_3916_, lean_object* v_inst_3917_, lean_object* v_toBind_3918_, lean_object* v_a_3919_, lean_object* v_x_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_snd_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3942_; 
v_snd_3922_ = lean_ctor_get(v___y_3921_, 1);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___y_3921_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v___y_3921_, 0);
lean_dec(v_unused_3943_);
v___x_3924_ = v___y_3921_;
v_isShared_3925_ = v_isSharedCheck_3942_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_snd_3922_);
lean_dec(v___y_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3942_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
if (lean_obj_tag(v_snd_3922_) == 6)
{
lean_object* v_binderType_3926_; lean_object* v_body_3927_; lean_object* v___f_3928_; 
lean_del_object(v___x_3924_);
v_binderType_3926_ = lean_ctor_get(v_snd_3922_, 1);
lean_inc_ref(v_binderType_3926_);
v_body_3927_ = lean_ctor_get(v_snd_3922_, 2);
lean_inc(v_toPure_3915_);
lean_inc(v___x_3914_);
lean_inc_ref(v_a_3919_);
lean_inc_ref(v_body_3927_);
v___f_3928_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3928_, 0, v_body_3927_);
lean_closure_set(v___f_3928_, 1, v_a_3919_);
lean_closure_set(v___f_3928_, 2, v___x_3914_);
lean_closure_set(v___f_3928_, 3, v_toPure_3915_);
if (lean_obj_tag(v_levels_x3f_3916_) == 0)
{
lean_object* v___f_3929_; lean_object* v___f_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v___x_3914_);
v___f_3929_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3929_, 0, v_snd_3922_);
lean_closure_set(v___f_3929_, 1, v_toPure_3915_);
lean_closure_set(v___f_3929_, 2, v___f_3928_);
lean_inc(v_toBind_3918_);
lean_inc(v_inst_3917_);
v___f_3930_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3930_, 0, v_binderType_3926_);
lean_closure_set(v___f_3930_, 1, v_inst_3917_);
lean_closure_set(v___f_3930_, 2, v_toBind_3918_);
lean_closure_set(v___f_3930_, 3, v___f_3929_);
v___x_3931_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3931_, 0, v_a_3919_);
v___x_3932_ = lean_apply_2(v_inst_3917_, lean_box(0), v___x_3931_);
v___x_3933_ = lean_apply_4(v_toBind_3918_, lean_box(0), lean_box(0), v___x_3932_, v___f_3930_);
return v___x_3933_;
}
else
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_inc_ref(v_body_3927_);
lean_dec_ref(v___f_3928_);
lean_dec_ref(v_binderType_3926_);
lean_dec_ref_known(v_snd_3922_, 3);
lean_dec(v_toBind_3918_);
lean_dec(v_inst_3917_);
v___x_3934_ = lean_box(0);
v___x_3935_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3927_, v_a_3919_, v___x_3914_, v_toPure_3915_, v___x_3934_);
lean_dec_ref(v_a_3919_);
lean_dec_ref(v_body_3927_);
return v___x_3935_;
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
lean_dec_ref(v_a_3919_);
lean_dec(v_toBind_3918_);
lean_dec(v_inst_3917_);
lean_dec(v___x_3914_);
v___x_3936_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3936_);
v___x_3938_ = v___x_3924_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_snd_3922_);
v___x_3938_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
v___x_3940_ = lean_apply_2(v_toPure_3915_, lean_box(0), v___x_3939_);
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3944_, lean_object* v_toPure_3945_, lean_object* v_levels_x3f_3946_, lean_object* v_inst_3947_, lean_object* v_toBind_3948_, lean_object* v_a_3949_, lean_object* v_x_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3944_, v_toPure_3945_, v_levels_x3f_3946_, v_inst_3947_, v_toBind_3948_, v_a_3949_, v_x_3950_, v___y_3951_);
lean_dec(v_levels_x3f_3946_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3953_, lean_object* v_levels_x3f_3954_, lean_object* v_inst_3955_, lean_object* v_toBind_3956_, lean_object* v_params_3957_, lean_object* v_inst_3958_, lean_object* v___f_3959_, lean_object* v_val_3960_){
_start:
{
lean_object* v___x_3961_; lean_object* v___f_3962_; lean_object* v___x_3963_; size_t v_sz_3964_; size_t v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3961_ = lean_box(0);
lean_inc(v_toBind_3956_);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3962_, 0, v___x_3961_);
lean_closure_set(v___f_3962_, 1, v_toPure_3953_);
lean_closure_set(v___f_3962_, 2, v_levels_x3f_3954_);
lean_closure_set(v___f_3962_, 3, v_inst_3955_);
lean_closure_set(v___f_3962_, 4, v_toBind_3956_);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3961_);
lean_ctor_set(v___x_3963_, 1, v_val_3960_);
v_sz_3964_ = lean_array_size(v_params_3957_);
v___x_3965_ = ((size_t)0ULL);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3958_, v_params_3957_, v___f_3962_, v_sz_3964_, v___x_3965_, v___x_3963_);
v___x_3967_ = lean_apply_4(v_toBind_3956_, lean_box(0), lean_box(0), v___x_3966_, v___f_3959_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3968_, lean_object* v_us_3969_, uint8_t v___x_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3968_, v_us_3969_, v___x_3970_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3977_, lean_object* v_us_3978_, lean_object* v___x_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v___x_677__boxed_3985_; lean_object* v_res_3986_; 
v___x_677__boxed_3985_ = lean_unbox(v___x_3979_);
v_res_3986_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3977_, v_us_3978_, v___x_677__boxed_3985_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v_cinfo_3977_);
return v_res_3986_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3990_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_3991_ = lean_unsigned_to_nat(2u);
v___x_3992_ = lean_unsigned_to_nat(202u);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_3994_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_3995_ = l_mkPanicMessageWithDecl(v___x_3994_, v___x_3993_, v___x_3992_, v___x_3991_, v___x_3990_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_3996_, lean_object* v___x_3997_, lean_object* v_inst_3998_, lean_object* v_toBind_3999_, lean_object* v___f_4000_, lean_object* v_us_4001_){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4002_ = l_List_lengthTR___redArg(v_us_4001_);
v___x_4003_ = l_Lean_ConstantInfo_levelParams(v_cinfo_3996_);
v___x_4004_ = l_List_lengthTR___redArg(v___x_4003_);
lean_dec(v___x_4003_);
v___x_4005_ = lean_nat_dec_eq(v___x_4002_, v___x_4004_);
lean_dec(v___x_4004_);
lean_dec(v___x_4002_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec(v_us_4001_);
lean_dec(v___f_4000_);
lean_dec(v_toBind_3999_);
lean_dec(v_inst_3998_);
lean_dec_ref(v_cinfo_3996_);
v___x_4006_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4007_ = l_panic___redArg(v___x_3997_, v___x_4006_);
return v___x_4007_;
}
else
{
uint8_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___f_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4008_ = 0;
v___x_4009_ = lean_box(v___x_4008_);
v___f_4010_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4010_, 0, v_cinfo_3996_);
lean_closure_set(v___f_4010_, 1, v_us_4001_);
lean_closure_set(v___f_4010_, 2, v___x_4009_);
v___x_4011_ = lean_apply_2(v_inst_3998_, lean_box(0), v___f_4010_);
v___x_4012_ = lean_apply_4(v_toBind_3999_, lean_box(0), lean_box(0), v___x_4011_, v___f_4000_);
return v___x_4012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4013_, lean_object* v___x_4014_, lean_object* v_inst_4015_, lean_object* v_toBind_4016_, lean_object* v___f_4017_, lean_object* v_us_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4013_, v___x_4014_, v_inst_4015_, v_toBind_4016_, v___f_4017_, v_us_4018_);
lean_dec(v___x_4014_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4020_, lean_object* v_inst_4021_, lean_object* v_toBind_4022_, lean_object* v___f_4023_, lean_object* v_levels_x3f_4024_, lean_object* v_toPure_4025_, lean_object* v_cinfo_4026_){
_start:
{
lean_object* v___f_4027_; 
lean_inc(v_toBind_4022_);
lean_inc(v_inst_4021_);
lean_inc_ref(v_cinfo_4026_);
v___f_4027_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4027_, 0, v_cinfo_4026_);
lean_closure_set(v___f_4027_, 1, v___x_4020_);
lean_closure_set(v___f_4027_, 2, v_inst_4021_);
lean_closure_set(v___f_4027_, 3, v_toBind_4022_);
lean_closure_set(v___f_4027_, 4, v___f_4023_);
if (lean_obj_tag(v_levels_x3f_4024_) == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec(v_toPure_4025_);
v___x_4028_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4028_, 0, v_cinfo_4026_);
v___x_4029_ = lean_apply_2(v_inst_4021_, lean_box(0), v___x_4028_);
v___x_4030_ = lean_apply_4(v_toBind_4022_, lean_box(0), lean_box(0), v___x_4029_, v___f_4027_);
return v___x_4030_;
}
else
{
lean_object* v_val_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec_ref(v_cinfo_4026_);
lean_dec(v_inst_4021_);
v_val_4031_ = lean_ctor_get(v_levels_x3f_4024_, 0);
lean_inc(v_val_4031_);
lean_dec_ref_known(v_levels_x3f_4024_, 1);
v___x_4032_ = lean_apply_2(v_toPure_4025_, lean_box(0), v_val_4031_);
v___x_4033_ = lean_apply_4(v_toBind_4022_, lean_box(0), lean_box(0), v___x_4032_, v___f_4027_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4034_, lean_object* v_inst_4035_, lean_object* v_inst_4036_, lean_object* v_inst_4037_, lean_object* v_defaultFn_4038_, lean_object* v_levels_x3f_4039_, lean_object* v_params_4040_, lean_object* v_fieldVal_x3f_4041_){
_start:
{
lean_object* v_toApplicative_4042_; lean_object* v_toBind_4043_; lean_object* v_toPure_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___f_4047_; lean_object* v___f_4048_; lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___x_4051_; 
v_toApplicative_4042_ = lean_ctor_get(v_inst_4034_, 0);
v_toBind_4043_ = lean_ctor_get(v_inst_4034_, 1);
lean_inc_n(v_toBind_4043_, 3);
v_toPure_4044_ = lean_ctor_get(v_toApplicative_4042_, 1);
lean_inc_n(v_toPure_4044_, 3);
v___x_4045_ = lean_box(0);
lean_inc_ref_n(v_inst_4034_, 3);
v___x_4046_ = l_Lean_getConstInfo___redArg(v_inst_4034_, v_inst_4035_, v_inst_4036_, v_defaultFn_4038_);
lean_inc_n(v_inst_4037_, 2);
v___f_4047_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4047_, 0, v_inst_4034_);
lean_closure_set(v___f_4047_, 1, v_inst_4037_);
lean_closure_set(v___f_4047_, 2, v_fieldVal_x3f_4041_);
lean_closure_set(v___f_4047_, 3, v_toPure_4044_);
lean_inc(v_levels_x3f_4039_);
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4048_, 0, v_toPure_4044_);
lean_closure_set(v___f_4048_, 1, v_levels_x3f_4039_);
lean_closure_set(v___f_4048_, 2, v_inst_4037_);
lean_closure_set(v___f_4048_, 3, v_toBind_4043_);
lean_closure_set(v___f_4048_, 4, v_params_4040_);
lean_closure_set(v___f_4048_, 5, v_inst_4034_);
lean_closure_set(v___f_4048_, 6, v___f_4047_);
v___x_4049_ = l_instInhabitedOfMonad___redArg(v_inst_4034_, v___x_4045_);
v___f_4050_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4050_, 0, v___x_4049_);
lean_closure_set(v___f_4050_, 1, v_inst_4037_);
lean_closure_set(v___f_4050_, 2, v_toBind_4043_);
lean_closure_set(v___f_4050_, 3, v___f_4048_);
lean_closure_set(v___f_4050_, 4, v_levels_x3f_4039_);
lean_closure_set(v___f_4050_, 5, v_toPure_4044_);
v___x_4051_ = lean_apply_4(v_toBind_4043_, lean_box(0), lean_box(0), v___x_4046_, v___f_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4052_, lean_object* v_inst_4053_, lean_object* v_inst_4054_, lean_object* v_inst_4055_, lean_object* v_inst_4056_, lean_object* v_inst_4057_, lean_object* v_defaultFn_4058_, lean_object* v_levels_x3f_4059_, lean_object* v_params_4060_, lean_object* v_fieldVal_x3f_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4053_, v_inst_4054_, v_inst_4055_, v_inst_4056_, v_defaultFn_4058_, v_levels_x3f_4059_, v_params_4060_, v_fieldVal_x3f_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_inst_4066_, lean_object* v_inst_4067_, lean_object* v_inst_4068_, lean_object* v_defaultFn_4069_, lean_object* v_levels_x3f_4070_, lean_object* v_params_4071_, lean_object* v_fieldVal_x3f_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4063_, v_inst_4064_, v_inst_4065_, v_inst_4066_, v_inst_4067_, v_inst_4068_, v_defaultFn_4069_, v_levels_x3f_4070_, v_params_4071_, v_fieldVal_x3f_4072_);
lean_dec_ref(v_inst_4068_);
return v_res_4073_;
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
