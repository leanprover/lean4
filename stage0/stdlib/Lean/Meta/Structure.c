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
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__0));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__3(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__2));
v___x_57_ = l_Lean_stringToMessageData(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Meta_getStructureName___closed__5(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_getStructureName___closed__4));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
lean_object* l_Lean_Meta_getStructureName(lean_object* v_struct_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Expr_getAppFn(v_struct_61_);
if (lean_obj_tag(v___x_67_) == 4)
{
lean_object* v_declName_68_; lean_object* v___x_69_; lean_object* v_env_70_; uint8_t v___x_71_; 
v_declName_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc_n(v_declName_68_, 2);
lean_dec_ref_known(v___x_67_, 2);
v___x_69_ = lean_st_ref_get(v_a_65_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = l_Lean_isStructure(v_env_70_, v_declName_68_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v___x_72_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_73_ = l_Lean_MessageData_ofConstName(v_declName_68_, v___x_71_);
v___x_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__3, &l_Lean_Meta_getStructureName___closed__3_once, _init_l_Lean_Meta_getStructureName___closed__3);
v___x_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_76_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_declName_68_);
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec_ref(v___x_67_);
v___x_87_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__5, &l_Lean_Meta_getStructureName___closed__5_once, _init_l_Lean_Meta_getStructureName___closed__5);
v___x_88_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_87_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
return v___x_88_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getStructureName_0interp(lean_interpreter_value* stack)
{
lean_object* v_struct_61_ = stack[0].m_obj;
lean_object* v_a_62_ = stack[1].m_obj;
lean_object* v_a_63_ = stack[2].m_obj;
lean_object* v_a_64_ = stack[3].m_obj;
lean_object* v_a_65_ = stack[4].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_Meta_getStructureName(v_struct_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getStructureName___boxed(lean_object* v_struct_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_getStructureName(v_struct_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec_ref(v_struct_90_);
return v_res_96_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_object* v_00_u03b1_97_, lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_98_ = stack[1].m_obj;
lean_object* v___y_99_ = stack[2].m_obj;
lean_object* v___y_100_ = stack[3].m_obj;
lean_object* v___y_101_ = stack[4].m_obj;
lean_object* v___y_102_ = stack[5].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(lean_box(0), v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(lean_object* v_00_u03b1_106_, lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(v_00_u03b1_106_, v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(lean_object* v_name_114_, lean_object* v_levelParams_115_, lean_object* v_type_116_, lean_object* v_value_117_, lean_object* v_hints_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; uint8_t v___y_123_; uint8_t v___y_130_; lean_object* v_env_133_; uint8_t v___x_134_; 
v___x_121_ = lean_st_ref_get(v___y_119_);
v_env_133_ = lean_ctor_get(v___x_121_, 0);
lean_inc_ref_n(v_env_133_, 2);
lean_dec(v___x_121_);
v___x_134_ = l_Lean_Environment_hasUnsafe(v_env_133_, v_type_116_);
if (v___x_134_ == 0)
{
uint8_t v___x_135_; 
v___x_135_ = l_Lean_Environment_hasUnsafe(v_env_133_, v_value_117_);
v___y_130_ = v___x_135_;
goto v___jp_129_;
}
else
{
lean_dec_ref(v_env_133_);
v___y_130_ = v___x_134_;
goto v___jp_129_;
}
v___jp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_inc(v_name_114_);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v_name_114_);
lean_ctor_set(v___x_124_, 1, v_levelParams_115_);
lean_ctor_set(v___x_124_, 2, v_type_116_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v_name_114_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v_value_117_);
lean_ctor_set(v___x_127_, 2, v_hints_118_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*4, v___y_123_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
v___jp_129_:
{
if (v___y_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 1;
v___y_123_ = v___x_131_;
goto v___jp_122_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
v___y_123_ = v___x_132_;
goto v___jp_122_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_114_ = stack[0].m_obj;
lean_object* v_levelParams_115_ = stack[1].m_obj;
lean_object* v_type_116_ = stack[2].m_obj;
lean_object* v_value_117_ = stack[3].m_obj;
lean_object* v_hints_118_ = stack[4].m_obj;
lean_object* v___y_119_ = stack[5].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_114_, v_levelParams_115_, v_type_116_, v_value_117_, v_hints_118_, v___y_119_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v_name_137_, lean_object* v_levelParams_138_, lean_object* v_type_139_, lean_object* v_value_140_, lean_object* v_hints_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_137_, v_levelParams_138_, v_type_139_, v_value_140_, v_hints_141_, v___y_142_);
lean_dec(v___y_142_);
return v_res_144_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_name_145_, lean_object* v_levelParams_146_, lean_object* v_type_147_, lean_object* v_value_148_, lean_object* v_hints_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_145_, v_levelParams_146_, v_type_147_, v_value_148_, v_hints_149_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_145_ = stack[0].m_obj;
lean_object* v_levelParams_146_ = stack[1].m_obj;
lean_object* v_type_147_ = stack[2].m_obj;
lean_object* v_value_148_ = stack[3].m_obj;
lean_object* v_hints_149_ = stack[4].m_obj;
lean_object* v___y_150_ = stack[5].m_obj;
lean_object* v___y_151_ = stack[6].m_obj;
lean_object* v___y_152_ = stack[7].m_obj;
lean_object* v___y_153_ = stack[8].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_145_, v_levelParams_146_, v_type_147_, v_value_148_, v_hints_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object* v_name_157_, lean_object* v_levelParams_158_, lean_object* v_type_159_, lean_object* v_value_160_, lean_object* v_hints_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_157_, v_levelParams_158_, v_type_159_, v_value_160_, v_hints_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_167_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v_k_168_, lean_object* v_b_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_175_ = lean_apply_6(v_k_168_, v_b_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
return v___x_175_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_168_ = stack[0].m_obj;
lean_object* v_b_169_ = stack[1].m_obj;
lean_object* v___y_170_ = stack[2].m_obj;
lean_object* v___y_171_ = stack[3].m_obj;
lean_object* v___y_172_ = stack[4].m_obj;
lean_object* v___y_173_ = stack[5].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_168_, v_b_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_177_, lean_object* v_b_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_177_, v_b_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_name_185_, uint8_t v_bi_186_, lean_object* v_type_187_, lean_object* v_k_188_, uint8_t v_kind_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___f_195_; lean_object* v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_195_, 0, v_k_188_);
v___x_196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_185_, v_bi_186_, v_type_187_, v___f_195_, v_kind_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
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
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_196_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_196_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_185_ = stack[0].m_obj;
uint8_t v_bi_186_ = stack[1].m_num;
lean_object* v_type_187_ = stack[2].m_obj;
lean_object* v_k_188_ = stack[3].m_obj;
uint8_t v_kind_189_ = stack[4].m_num;
lean_object* v___y_190_ = stack[5].m_obj;
lean_object* v___y_191_ = stack[6].m_obj;
lean_object* v___y_192_ = stack[7].m_obj;
lean_object* v___y_193_ = stack[8].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_185_, v_bi_186_, v_type_187_, v_k_188_, v_kind_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object* v_name_214_, lean_object* v_bi_215_, lean_object* v_type_216_, lean_object* v_k_217_, lean_object* v_kind_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
uint8_t v_bi_boxed_224_; uint8_t v_kind_boxed_225_; lean_object* v_res_226_; 
v_bi_boxed_224_ = lean_unbox(v_bi_215_);
v_kind_boxed_225_ = lean_unbox(v_kind_218_);
v_res_226_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_214_, v_bi_boxed_224_, v_type_216_, v_k_217_, v_kind_boxed_225_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_226_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_00_u03b1_227_, lean_object* v_name_228_, uint8_t v_bi_229_, lean_object* v_type_230_, lean_object* v_k_231_, uint8_t v_kind_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_228_, v_bi_229_, v_type_230_, v_k_231_, v_kind_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_228_ = stack[1].m_obj;
uint8_t v_bi_229_ = stack[2].m_num;
lean_object* v_type_230_ = stack[3].m_obj;
lean_object* v_k_231_ = stack[4].m_obj;
uint8_t v_kind_232_ = stack[5].m_num;
lean_object* v___y_233_ = stack[6].m_obj;
lean_object* v___y_234_ = stack[7].m_obj;
lean_object* v___y_235_ = stack[8].m_obj;
lean_object* v___y_236_ = stack[9].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_box(0), v_name_228_, v_bi_229_, v_type_230_, v_k_231_, v_kind_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object* v_00_u03b1_240_, lean_object* v_name_241_, lean_object* v_bi_242_, lean_object* v_type_243_, lean_object* v_k_244_, lean_object* v_kind_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
uint8_t v_bi_boxed_251_; uint8_t v_kind_boxed_252_; lean_object* v_res_253_; 
v_bi_boxed_251_ = lean_unbox(v_bi_242_);
v_kind_boxed_252_ = lean_unbox(v_kind_245_);
v_res_253_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(v_00_u03b1_240_, v_name_241_, v_bi_boxed_251_, v_type_243_, v_k_244_, v_kind_boxed_252_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_253_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_254_, lean_object* v_b_255_, lean_object* v_c_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
lean_inc(v___y_260_);
lean_inc_ref(v___y_259_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
v___x_262_ = lean_apply_7(v_k_254_, v_b_255_, v_c_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, lean_box(0));
return v___x_262_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_254_ = stack[0].m_obj;
lean_object* v_b_255_ = stack[1].m_obj;
lean_object* v_c_256_ = stack[2].m_obj;
lean_object* v___y_257_ = stack[3].m_obj;
lean_object* v___y_258_ = stack[4].m_obj;
lean_object* v___y_259_ = stack[5].m_obj;
lean_object* v___y_260_ = stack[6].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_254_, v_b_255_, v_c_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_264_, lean_object* v_b_265_, lean_object* v_c_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_264_, v_b_265_, v_c_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_type_273_, lean_object* v_maxFVars_x3f_274_, lean_object* v_k_275_, uint8_t v_cleanupAnnotations_276_, uint8_t v_whnfType_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_284_; 
v___f_283_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_283_, 0, v_k_275_);
v___x_284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_273_, v_maxFVars_x3f_274_, v___f_283_, v_cleanupAnnotations_276_, v_whnfType_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_284_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_284_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_273_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_274_ = stack[1].m_obj;
lean_object* v_k_275_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_276_ = stack[3].m_num;
uint8_t v_whnfType_277_ = stack[4].m_num;
lean_object* v___y_278_ = stack[5].m_obj;
lean_object* v___y_279_ = stack[6].m_obj;
lean_object* v___y_280_ = stack[7].m_obj;
lean_object* v___y_281_ = stack[8].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_273_, v_maxFVars_x3f_274_, v_k_275_, v_cleanupAnnotations_276_, v_whnfType_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_type_302_, lean_object* v_maxFVars_x3f_303_, lean_object* v_k_304_, lean_object* v_cleanupAnnotations_305_, lean_object* v_whnfType_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_312_; uint8_t v_whnfType_boxed_313_; lean_object* v_res_314_; 
v_cleanupAnnotations_boxed_312_ = lean_unbox(v_cleanupAnnotations_305_);
v_whnfType_boxed_313_ = lean_unbox(v_whnfType_306_);
v_res_314_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_302_, v_maxFVars_x3f_303_, v_k_304_, v_cleanupAnnotations_boxed_312_, v_whnfType_boxed_313_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
return v_res_314_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_315_, lean_object* v_type_316_, lean_object* v_maxFVars_x3f_317_, lean_object* v_k_318_, uint8_t v_cleanupAnnotations_319_, uint8_t v_whnfType_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_316_, v_maxFVars_x3f_317_, v_k_318_, v_cleanupAnnotations_319_, v_whnfType_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_316_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_317_ = stack[2].m_obj;
lean_object* v_k_318_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_319_ = stack[4].m_num;
uint8_t v_whnfType_320_ = stack[5].m_num;
lean_object* v___y_321_ = stack[6].m_obj;
lean_object* v___y_322_ = stack[7].m_obj;
lean_object* v___y_323_ = stack[8].m_obj;
lean_object* v___y_324_ = stack[9].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_box(0), v_type_316_, v_maxFVars_x3f_317_, v_k_318_, v_cleanupAnnotations_319_, v_whnfType_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_328_, lean_object* v_type_329_, lean_object* v_maxFVars_x3f_330_, lean_object* v_k_331_, lean_object* v_cleanupAnnotations_332_, lean_object* v_whnfType_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_339_; uint8_t v_whnfType_boxed_340_; lean_object* v_res_341_; 
v_cleanupAnnotations_boxed_339_ = lean_unbox(v_cleanupAnnotations_332_);
v_whnfType_boxed_340_ = lean_unbox(v_whnfType_333_);
v_res_341_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_328_, v_type_329_, v_maxFVars_x3f_330_, v_k_331_, v_cleanupAnnotations_boxed_339_, v_whnfType_boxed_340_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_341_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_lctx_342_, lean_object* v_localInsts_343_, lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_342_, v_localInsts_343_, v_x_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_350_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_350_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_342_ = stack[0].m_obj;
lean_object* v_localInsts_343_ = stack[1].m_obj;
lean_object* v_x_344_ = stack[2].m_obj;
lean_object* v___y_345_ = stack[3].m_obj;
lean_object* v___y_346_ = stack[4].m_obj;
lean_object* v___y_347_ = stack[5].m_obj;
lean_object* v___y_348_ = stack[6].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_342_, v_localInsts_343_, v_x_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_lctx_368_, lean_object* v_localInsts_369_, lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_368_, v_localInsts_369_, v_x_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_377_, lean_object* v_lctx_378_, lean_object* v_localInsts_379_, lean_object* v_x_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_378_, v_localInsts_379_, v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_378_ = stack[1].m_obj;
lean_object* v_localInsts_379_ = stack[2].m_obj;
lean_object* v_x_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v___y_382_ = stack[5].m_obj;
lean_object* v___y_383_ = stack[6].m_obj;
lean_object* v___y_384_ = stack[7].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_box(0), v_lctx_378_, v_localInsts_379_, v_x_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_388_, lean_object* v_lctx_389_, lean_object* v_localInsts_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_388_, v_lctx_389_, v_localInsts_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_398_, lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_toCold_405_; lean_object* v_currRecDepth_406_; lean_object* v_ref_407_; uint16_t v_optionFlags_408_; uint8_t v_suppressElabErrors_409_; uint8_t v_isRecordingDeps_410_; lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_toCold_405_ = lean_ctor_get(v___y_402_, 0);
v_currRecDepth_406_ = lean_ctor_get(v___y_402_, 1);
v_ref_407_ = lean_ctor_get(v___y_402_, 2);
v_optionFlags_408_ = lean_ctor_get_uint16(v___y_402_, sizeof(void*)*3);
v_suppressElabErrors_409_ = lean_ctor_get_uint8(v___y_402_, sizeof(void*)*3 + 2);
v_isRecordingDeps_410_ = lean_ctor_get_uint8(v___y_402_, sizeof(void*)*3 + 3);
v_ref_411_ = l_Lean_replaceRef(v_ref_398_, v_ref_407_);
lean_inc(v_currRecDepth_406_);
lean_inc_ref(v_toCold_405_);
v___x_412_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_412_, 0, v_toCold_405_);
lean_ctor_set(v___x_412_, 1, v_currRecDepth_406_);
lean_ctor_set(v___x_412_, 2, v_ref_411_);
lean_ctor_set_uint16(v___x_412_, sizeof(void*)*3, v_optionFlags_408_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3 + 2, v_suppressElabErrors_409_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3 + 3, v_isRecordingDeps_410_);
v___x_413_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_399_, v___y_400_, v___y_401_, v___x_412_, v___y_403_);
lean_dec_ref_known(v___x_412_, 3);
return v___x_413_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_398_ = stack[0].m_obj;
lean_object* v_msg_399_ = stack[1].m_obj;
lean_object* v___y_400_ = stack[2].m_obj;
lean_object* v___y_401_ = stack[3].m_obj;
lean_object* v___y_402_ = stack[4].m_obj;
lean_object* v___y_403_ = stack[5].m_obj;
lean_object* v_res_414_;
v_res_414_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_398_, v_msg_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_415_, v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_ref_415_);
return v_res_422_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_425_ = l_Lean_stringToMessageData(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_432_, lean_object* v_projName_433_, lean_object* v_n_434_, lean_object* v_ref_435_, lean_object* v___f_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
if (v___x_432_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_442_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_443_ = l_Lean_MessageData_ofName(v_projName_433_);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = l_Lean_MessageData_ofConstName(v_n_434_, v___x_432_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_435_, v___x_450_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
v___x_453_ = lean_apply_6(v___f_436_, v_a_452_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, lean_box(0));
return v___x_453_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v___f_436_);
v_a_454_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_451_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_451_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_n_434_);
lean_dec(v_projName_433_);
v___x_462_ = lean_box(0);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
v___x_463_ = lean_apply_6(v___f_436_, v___x_462_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, lean_box(0));
return v___x_463_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_432_ = stack[0].m_num;
lean_object* v_projName_433_ = stack[1].m_obj;
lean_object* v_n_434_ = stack[2].m_obj;
lean_object* v_ref_435_ = stack[3].m_obj;
lean_object* v___f_436_ = stack[4].m_obj;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_432_, v_projName_433_, v_n_434_, v_ref_435_, v___f_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_465_, lean_object* v_projName_466_, lean_object* v_n_467_, lean_object* v_ref_468_, lean_object* v___f_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
uint8_t v___x_17227__boxed_475_; lean_object* v_res_476_; 
v___x_17227__boxed_475_ = lean_unbox(v___x_465_);
v_res_476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17227__boxed_475_, v_projName_466_, v_n_467_, v_ref_468_, v___f_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v_ref_468_);
return v_res_476_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_477_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_483_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_ctor_set(v___x_483_, 3, v___x_482_);
lean_ctor_set(v___x_483_, 4, v___x_482_);
lean_ctor_set(v___x_483_, 5, v___x_482_);
return v___x_483_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_484_, uint8_t v_s_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; lean_object* v_env_490_; lean_object* v_nextMacroScope_491_; lean_object* v_ngen_492_; lean_object* v_auxDeclNGen_493_; lean_object* v_traceState_494_; lean_object* v_recordedDeps_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_527_; 
v___x_489_ = lean_st_ref_take(v___y_487_);
v_env_490_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_491_ = lean_ctor_get(v___x_489_, 1);
v_ngen_492_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_493_ = lean_ctor_get(v___x_489_, 3);
v_traceState_494_ = lean_ctor_get(v___x_489_, 4);
v_recordedDeps_495_ = lean_ctor_get(v___x_489_, 6);
v_messages_496_ = lean_ctor_get(v___x_489_, 7);
v_infoState_497_ = lean_ctor_get(v___x_489_, 8);
v_snapshotTasks_498_ = lean_ctor_get(v___x_489_, 9);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_489_, 5);
lean_dec(v_unused_528_);
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_527_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_recordedDeps_495_);
lean_inc(v_traceState_494_);
lean_inc(v_auxDeclNGen_493_);
lean_inc(v_ngen_492_);
lean_inc(v_nextMacroScope_491_);
lean_inc(v_env_490_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_527_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_502_ = 0;
v___x_503_ = lean_box(0);
v___x_504_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_490_, v_declName_484_, v_s_485_, v___x_502_, v___x_503_);
v___x_505_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 5, v___x_505_);
lean_ctor_set(v___x_500_, 0, v___x_504_);
v___x_507_ = v___x_500_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_nextMacroScope_491_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_ngen_492_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_auxDeclNGen_493_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v_traceState_494_);
lean_ctor_set(v_reuseFailAlloc_526_, 5, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_526_, 6, v_recordedDeps_495_);
lean_ctor_set(v_reuseFailAlloc_526_, 7, v_messages_496_);
lean_ctor_set(v_reuseFailAlloc_526_, 8, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_526_, 9, v_snapshotTasks_498_);
v___x_507_ = v_reuseFailAlloc_526_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_mctx_510_; lean_object* v_zetaDeltaFVarIds_511_; lean_object* v_postponed_512_; lean_object* v_diag_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_524_; 
v___x_508_ = lean_st_ref_put(v___y_487_, v___x_507_);
v___x_509_ = lean_st_ref_take(v___y_486_);
v_mctx_510_ = lean_ctor_get(v___x_509_, 0);
v_zetaDeltaFVarIds_511_ = lean_ctor_get(v___x_509_, 2);
v_postponed_512_ = lean_ctor_get(v___x_509_, 3);
v_diag_513_ = lean_ctor_get(v___x_509_, 4);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_509_, 1);
lean_dec(v_unused_525_);
v___x_515_ = v___x_509_;
v_isShared_516_ = v_isSharedCheck_524_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_diag_513_);
lean_inc(v_postponed_512_);
lean_inc(v_zetaDeltaFVarIds_511_);
lean_inc(v_mctx_510_);
lean_dec(v___x_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_524_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_517_ = lean_box(0);
v___x_518_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v___x_518_);
v___x_520_ = v___x_515_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_mctx_510_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_zetaDeltaFVarIds_511_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_postponed_512_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_diag_513_);
v___x_520_ = v_reuseFailAlloc_523_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_st_ref_put(v___y_486_, v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_517_);
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_484_ = stack[0].m_obj;
uint8_t v_s_485_ = stack[1].m_num;
lean_object* v___y_486_ = stack[2].m_obj;
lean_object* v___y_487_ = stack[3].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_484_, v_s_485_, v___y_486_, v___y_487_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_530_, lean_object* v_s_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v_s_boxed_535_; lean_object* v_res_536_; 
v_s_boxed_535_ = lean_unbox(v_s_531_);
v_res_536_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_530_, v_s_boxed_535_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec(v___y_532_);
return v_res_536_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_543_ = 0;
v___x_544_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_537_, v___x_543_, v___y_539_, v___y_541_);
return v___x_544_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_537_ = stack[0].m_obj;
lean_object* v___y_538_ = stack[1].m_obj;
lean_object* v___y_539_ = stack[2].m_obj;
lean_object* v___y_540_ = stack[3].m_obj;
lean_object* v___y_541_ = stack[4].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_555_ = l_Lean_stringToMessageData(v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_562_, lean_object* v_projName_563_, lean_object* v___x_564_, lean_object* v_a_565_, uint8_t v_instImplicit_566_, lean_object* v___x_567_, lean_object* v_params_568_, lean_object* v_self_569_, lean_object* v_b_570_, uint8_t v___x_571_, lean_object* v_a_572_, lean_object* v___x_573_, lean_object* v_paramInfoOverrides_574_, lean_object* v_n_575_, lean_object* v_ref_576_, lean_object* v___x_577_, uint8_t v_a_578_, lean_object* v_____r_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = l_List_lengthTR___redArg(v_paramInfoOverrides_574_);
v___x_740_ = lean_array_get_size(v_params_568_);
v___x_741_ = lean_nat_dec_le(v___x_739_, v___x_740_);
lean_dec(v___x_739_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_742_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_563_);
v___x_743_ = l_Lean_MessageData_ofName(v_projName_563_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
lean_inc(v_n_575_);
v___x_747_ = l_Lean_MessageData_ofConstName(v_n_575_, v___x_741_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_576_, v___x_750_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec_ref_known(v___x_751_, 1);
goto v___jp_700_;
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v___x_577_);
lean_dec(v_n_575_);
lean_dec_ref(v_a_572_);
lean_dec_ref(v_self_569_);
lean_dec(v___x_567_);
lean_dec(v_a_565_);
lean_dec(v___x_564_);
lean_dec(v_projName_563_);
lean_dec_ref(v___x_562_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
goto v___jp_700_;
}
v___jp_585_:
{
lean_object* v___x_588_; lean_object* v_env_589_; lean_object* v_nextMacroScope_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_traceState_593_; lean_object* v_recordedDeps_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_629_; 
v___x_588_ = lean_st_ref_take(v___y_587_);
v_env_589_ = lean_ctor_get(v___x_588_, 0);
v_nextMacroScope_590_ = lean_ctor_get(v___x_588_, 1);
v_ngen_591_ = lean_ctor_get(v___x_588_, 2);
v_auxDeclNGen_592_ = lean_ctor_get(v___x_588_, 3);
v_traceState_593_ = lean_ctor_get(v___x_588_, 4);
v_recordedDeps_594_ = lean_ctor_get(v___x_588_, 6);
v_messages_595_ = lean_ctor_get(v___x_588_, 7);
v_infoState_596_ = lean_ctor_get(v___x_588_, 8);
v_snapshotTasks_597_ = lean_ctor_get(v___x_588_, 9);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_588_, 5);
lean_dec(v_unused_630_);
v___x_599_ = v___x_588_;
v_isShared_600_ = v_isSharedCheck_629_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_recordedDeps_594_);
lean_inc(v_traceState_593_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_env_589_);
lean_dec(v___x_588_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_629_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_name_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_name_601_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_name_601_);
lean_dec_ref(v___x_562_);
lean_inc(v_projName_563_);
v___x_602_ = l_Lean_addProjectionFnInfo(v_env_589_, v_projName_563_, v_name_601_, v___x_564_, v_a_565_, v_instImplicit_566_);
v___x_603_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 5, v___x_603_);
lean_ctor_set(v___x_599_, 0, v___x_602_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v_traceState_593_);
lean_ctor_set(v_reuseFailAlloc_628_, 5, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_628_, 6, v_recordedDeps_594_);
lean_ctor_set(v_reuseFailAlloc_628_, 7, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_628_, 8, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_628_, 9, v_snapshotTasks_597_);
v___x_605_ = v_reuseFailAlloc_628_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_mctx_608_; lean_object* v_zetaDeltaFVarIds_609_; lean_object* v_postponed_610_; lean_object* v_diag_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_626_; 
v___x_606_ = lean_st_ref_put(v___y_587_, v___x_605_);
v___x_607_ = lean_st_ref_take(v___y_586_);
v_mctx_608_ = lean_ctor_get(v___x_607_, 0);
v_zetaDeltaFVarIds_609_ = lean_ctor_get(v___x_607_, 2);
v_postponed_610_ = lean_ctor_get(v___x_607_, 3);
v_diag_611_ = lean_ctor_get(v___x_607_, 4);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_607_, 1);
lean_dec(v_unused_627_);
v___x_613_ = v___x_607_;
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_diag_611_);
lean_inc(v_postponed_610_);
lean_inc(v_zetaDeltaFVarIds_609_);
lean_inc(v_mctx_608_);
lean_dec(v___x_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_mctx_608_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_zetaDeltaFVarIds_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_postponed_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_diag_611_);
v___x_617_ = v_reuseFailAlloc_625_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_618_ = lean_st_ref_put(v___y_586_, v___x_617_);
v___x_619_ = l_Lean_Expr_const___override(v_projName_563_, v___x_567_);
v___x_620_ = l_Lean_mkAppN(v___x_619_, v_params_568_);
v___x_621_ = l_Lean_Expr_app___override(v___x_620_, v_self_569_);
v___x_622_ = l_Lean_Expr_bindingBody_x21(v_b_570_);
v___x_623_ = lean_expr_instantiate1(v___x_622_, v___x_621_);
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
}
}
v___jp_631_:
{
if (lean_obj_tag(v___y_634_) == 0)
{
lean_dec_ref_known(v___y_634_, 1);
v___y_586_ = v___y_632_;
v___y_587_ = v___y_633_;
goto v___jp_585_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_self_569_);
lean_dec(v___x_567_);
lean_dec(v_a_565_);
lean_dec(v___x_564_);
lean_dec(v_projName_563_);
lean_dec_ref(v___x_562_);
v_a_635_ = lean_ctor_get(v___y_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___y_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___y_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___y_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
v___jp_643_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_650_ = lean_box(0);
lean_inc(v_projName_563_);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_projName_563_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_652_, 0, v___y_648_);
lean_ctor_set(v___x_652_, 1, v___y_645_);
lean_ctor_set(v___x_652_, 2, v___x_651_);
lean_ctor_set_uint8(v___x_652_, sizeof(void*)*3, v___x_571_);
v___x_653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
v___x_654_ = l_Lean_addDecl(v___x_653_, v___y_646_, v___y_644_, v___y_649_);
lean_dec_ref(v___y_644_);
v___y_632_ = v___y_647_;
v___y_633_ = v___y_649_;
v___y_634_ = v___x_654_;
goto v___jp_631_;
}
v___jp_655_:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v_toCold_664_; lean_object* v_currRecDepth_665_; lean_object* v_ref_666_; uint16_t v_optionFlags_667_; uint8_t v_suppressElabErrors_668_; uint8_t v_isRecordingDeps_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_ref_674_; lean_object* v___x_675_; 
v___x_662_ = 0;
lean_inc_ref(v_a_572_);
v___x_663_ = l_Lean_LocalContext_mkForall(v_a_572_, v___x_573_, v___y_656_, v___x_571_, v___x_662_);
lean_dec_ref(v___y_656_);
v_toCold_664_ = lean_ctor_get(v___y_660_, 0);
v_currRecDepth_665_ = lean_ctor_get(v___y_660_, 1);
v_ref_666_ = lean_ctor_get(v___y_660_, 2);
v_optionFlags_667_ = lean_ctor_get_uint16(v___y_660_, sizeof(void*)*3);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 2);
v_isRecordingDeps_669_ = lean_ctor_get_uint8(v___y_660_, sizeof(void*)*3 + 3);
v___x_670_ = l_Lean_Expr_inferImplicit(v___x_663_, v___x_564_, v___x_571_);
v___x_671_ = l_Lean_Expr_updateForallBinderInfos(v___x_670_, v_paramInfoOverrides_574_);
lean_inc_ref(v_self_569_);
lean_inc(v_a_565_);
v___x_672_ = l_Lean_Expr_proj___override(v_n_575_, v_a_565_, v_self_569_);
v___x_673_ = l_Lean_LocalContext_mkLambda(v_a_572_, v___x_573_, v___x_672_, v___x_571_, v___x_662_);
lean_dec_ref(v___x_672_);
v_ref_674_ = l_Lean_replaceRef(v_ref_576_, v_ref_666_);
lean_inc(v_currRecDepth_665_);
lean_inc_ref(v_toCold_664_);
v___x_675_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_675_, 0, v_toCold_664_);
lean_ctor_set(v___x_675_, 1, v_currRecDepth_665_);
lean_ctor_set(v___x_675_, 2, v_ref_674_);
lean_ctor_set_uint16(v___x_675_, sizeof(void*)*3, v_optionFlags_667_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*3 + 2, v_suppressElabErrors_668_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*3 + 3, v_isRecordingDeps_669_);
if (v___y_657_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_box(1);
lean_inc(v_projName_563_);
v___x_677_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_563_, v___x_577_, v___x_671_, v___x_673_, v___x_676_, v___y_661_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v_a_678_);
v___x_680_ = l_Lean_addDecl(v___x_679_, v___x_662_, v___x_675_, v___y_661_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref_known(v___x_680_, 1);
if (v_instImplicit_566_ == 0)
{
lean_object* v___x_681_; 
lean_inc(v_projName_563_);
v___x_681_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_563_, v___y_658_, v___y_659_, v___x_675_, v___y_661_);
lean_dec_ref_known(v___x_675_, 3);
v___y_632_ = v___y_659_;
v___y_633_ = v___y_661_;
v___y_634_ = v___x_681_;
goto v___jp_631_;
}
else
{
lean_dec_ref_known(v___x_675_, 3);
v___y_586_ = v___y_659_;
v___y_587_ = v___y_661_;
goto v___jp_585_;
}
}
else
{
lean_dec_ref_known(v___x_675_, 3);
v___y_632_ = v___y_659_;
v___y_633_ = v___y_661_;
v___y_634_ = v___x_680_;
goto v___jp_631_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref_known(v___x_675_, 3);
lean_dec_ref(v_self_569_);
lean_dec(v___x_567_);
lean_dec(v_a_565_);
lean_dec(v___x_564_);
lean_dec(v_projName_563_);
lean_dec_ref(v___x_562_);
v_a_682_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_677_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_env_692_; uint8_t v___x_693_; 
lean_inc_ref(v___x_671_);
lean_inc(v_projName_563_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v_projName_563_);
lean_ctor_set(v___x_690_, 1, v___x_577_);
lean_ctor_set(v___x_690_, 2, v___x_671_);
v___x_691_ = lean_st_ref_get(v___y_661_);
v_env_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref_n(v_env_692_, 2);
lean_dec(v___x_691_);
v___x_693_ = l_Lean_Environment_hasUnsafe(v_env_692_, v___x_671_);
lean_dec_ref(v___x_671_);
if (v___x_693_ == 0)
{
uint8_t v___x_694_; 
v___x_694_ = l_Lean_Environment_hasUnsafe(v_env_692_, v___x_673_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = lean_box(0);
lean_inc(v_projName_563_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v_projName_563_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_697_, 0, v___x_690_);
lean_ctor_set(v___x_697_, 1, v___x_673_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
v___x_698_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = l_Lean_addDecl(v___x_698_, v___x_662_, v___x_675_, v___y_661_);
lean_dec_ref_known(v___x_675_, 3);
v___y_632_ = v___y_659_;
v___y_633_ = v___y_661_;
v___y_634_ = v___x_699_;
goto v___jp_631_;
}
else
{
v___y_644_ = v___x_675_;
v___y_645_ = v___x_673_;
v___y_646_ = v___x_662_;
v___y_647_ = v___y_659_;
v___y_648_ = v___x_690_;
v___y_649_ = v___y_661_;
goto v___jp_643_;
}
}
else
{
lean_dec_ref(v_env_692_);
v___y_644_ = v___x_675_;
v___y_645_ = v___x_673_;
v___y_646_ = v___x_662_;
v___y_647_ = v___y_659_;
v___y_648_ = v___x_690_;
v___y_649_ = v___y_661_;
goto v___jp_643_;
}
}
}
v___jp_700_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = l_Lean_Expr_bindingDomain_x21(v_b_570_);
v___x_702_ = lean_expr_consume_type_annotations(v___x_701_);
lean_inc_ref(v___x_702_);
v___x_703_ = l_Lean_Meta_isProp(v___x_702_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_703_) == 0)
{
if (v_a_578_ == 0)
{
lean_object* v_a_704_; uint8_t v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
v___y_656_ = v___x_702_;
v___y_657_ = v___x_705_;
v___y_658_ = v___y_580_;
v___y_659_ = v___y_581_;
v___y_660_ = v___y_582_;
v___y_661_ = v___y_583_;
goto v___jp_655_;
}
else
{
lean_object* v_a_706_; uint8_t v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_703_, 1);
v___x_707_ = lean_unbox(v_a_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_708_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_563_);
v___x_709_ = l_Lean_MessageData_ofName(v_projName_563_);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_unbox(v_a_706_);
lean_inc(v_n_575_);
v___x_714_ = l_Lean_MessageData_ofConstName(v_n_575_, v___x_713_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_inc_ref(v___x_702_);
v___x_718_ = l_Lean_indentExpr(v___x_702_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_576_, v___x_719_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_720_) == 0)
{
uint8_t v___x_721_; 
lean_dec_ref_known(v___x_720_, 1);
v___x_721_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
v___y_656_ = v___x_702_;
v___y_657_ = v___x_721_;
v___y_658_ = v___y_580_;
v___y_659_ = v___y_581_;
v___y_660_ = v___y_582_;
v___y_661_ = v___y_583_;
goto v___jp_655_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_706_);
lean_dec_ref(v___x_702_);
lean_dec(v___x_577_);
lean_dec(v_n_575_);
lean_dec_ref(v_a_572_);
lean_dec_ref(v_self_569_);
lean_dec(v___x_567_);
lean_dec(v_a_565_);
lean_dec(v___x_564_);
lean_dec(v_projName_563_);
lean_dec_ref(v___x_562_);
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
else
{
uint8_t v___x_730_; 
v___x_730_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
v___y_656_ = v___x_702_;
v___y_657_ = v___x_730_;
v___y_658_ = v___y_580_;
v___y_659_ = v___y_581_;
v___y_660_ = v___y_582_;
v___y_661_ = v___y_583_;
goto v___jp_655_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___x_702_);
lean_dec(v___x_577_);
lean_dec(v_n_575_);
lean_dec_ref(v_a_572_);
lean_dec_ref(v_self_569_);
lean_dec(v___x_567_);
lean_dec(v_a_565_);
lean_dec(v___x_564_);
lean_dec(v_projName_563_);
lean_dec_ref(v___x_562_);
v_a_731_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_703_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_703_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_562_ = stack[0].m_obj;
lean_object* v_projName_563_ = stack[1].m_obj;
lean_object* v___x_564_ = stack[2].m_obj;
lean_object* v_a_565_ = stack[3].m_obj;
uint8_t v_instImplicit_566_ = stack[4].m_num;
lean_object* v___x_567_ = stack[5].m_obj;
lean_object* v_params_568_ = stack[6].m_obj;
lean_object* v_self_569_ = stack[7].m_obj;
lean_object* v_b_570_ = stack[8].m_obj;
uint8_t v___x_571_ = stack[9].m_num;
lean_object* v_a_572_ = stack[10].m_obj;
lean_object* v___x_573_ = stack[11].m_obj;
lean_object* v_paramInfoOverrides_574_ = stack[12].m_obj;
lean_object* v_n_575_ = stack[13].m_obj;
lean_object* v_ref_576_ = stack[14].m_obj;
lean_object* v___x_577_ = stack[15].m_obj;
uint8_t v_a_578_ = stack[16].m_num;
lean_object* v_____r_579_ = stack[17].m_obj;
lean_object* v___y_580_ = stack[18].m_obj;
lean_object* v___y_581_ = stack[19].m_obj;
lean_object* v___y_582_ = stack[20].m_obj;
lean_object* v___y_583_ = stack[21].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_562_, v_projName_563_, v___x_564_, v_a_565_, v_instImplicit_566_, v___x_567_, v_params_568_, v_self_569_, v_b_570_, v___x_571_, v_a_572_, v___x_573_, v_paramInfoOverrides_574_, v_n_575_, v_ref_576_, v___x_577_, v_a_578_, v_____r_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_761_ = _args[0];
lean_object* v_projName_762_ = _args[1];
lean_object* v___x_763_ = _args[2];
lean_object* v_a_764_ = _args[3];
lean_object* v_instImplicit_765_ = _args[4];
lean_object* v___x_766_ = _args[5];
lean_object* v_params_767_ = _args[6];
lean_object* v_self_768_ = _args[7];
lean_object* v_b_769_ = _args[8];
lean_object* v___x_770_ = _args[9];
lean_object* v_a_771_ = _args[10];
lean_object* v___x_772_ = _args[11];
lean_object* v_paramInfoOverrides_773_ = _args[12];
lean_object* v_n_774_ = _args[13];
lean_object* v_ref_775_ = _args[14];
lean_object* v___x_776_ = _args[15];
lean_object* v_a_777_ = _args[16];
lean_object* v_____r_778_ = _args[17];
lean_object* v___y_779_ = _args[18];
lean_object* v___y_780_ = _args[19];
lean_object* v___y_781_ = _args[20];
lean_object* v___y_782_ = _args[21];
lean_object* v___y_783_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_784_; uint8_t v___x_17567__boxed_785_; uint8_t v_a_17573__boxed_786_; lean_object* v_res_787_; 
v_instImplicit_boxed_784_ = lean_unbox(v_instImplicit_765_);
v___x_17567__boxed_785_ = lean_unbox(v___x_770_);
v_a_17573__boxed_786_ = lean_unbox(v_a_777_);
v_res_787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_761_, v_projName_762_, v___x_763_, v_a_764_, v_instImplicit_boxed_784_, v___x_766_, v_params_767_, v_self_768_, v_b_769_, v___x_17567__boxed_785_, v_a_771_, v___x_772_, v_paramInfoOverrides_773_, v_n_774_, v_ref_775_, v___x_776_, v_a_17573__boxed_786_, v_____r_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_ref_775_);
lean_dec(v_paramInfoOverrides_773_);
lean_dec_ref(v___x_772_);
lean_dec_ref(v_b_769_);
lean_dec_ref(v_params_767_);
return v_res_787_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_788_, uint8_t v_isExporting_789_, lean_object* v___x_790_, lean_object* v___y_791_, lean_object* v___x_792_, lean_object* v_a_x3f_793_){
_start:
{
lean_object* v___x_795_; lean_object* v_env_796_; lean_object* v_nextMacroScope_797_; lean_object* v_ngen_798_; lean_object* v_auxDeclNGen_799_; lean_object* v_traceState_800_; lean_object* v_recordedDeps_801_; lean_object* v_messages_802_; lean_object* v_infoState_803_; lean_object* v_snapshotTasks_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_829_; 
v___x_795_ = lean_st_ref_take(v___y_788_);
v_env_796_ = lean_ctor_get(v___x_795_, 0);
v_nextMacroScope_797_ = lean_ctor_get(v___x_795_, 1);
v_ngen_798_ = lean_ctor_get(v___x_795_, 2);
v_auxDeclNGen_799_ = lean_ctor_get(v___x_795_, 3);
v_traceState_800_ = lean_ctor_get(v___x_795_, 4);
v_recordedDeps_801_ = lean_ctor_get(v___x_795_, 6);
v_messages_802_ = lean_ctor_get(v___x_795_, 7);
v_infoState_803_ = lean_ctor_get(v___x_795_, 8);
v_snapshotTasks_804_ = lean_ctor_get(v___x_795_, 9);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_795_, 5);
lean_dec(v_unused_830_);
v___x_806_ = v___x_795_;
v_isShared_807_ = v_isSharedCheck_829_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snapshotTasks_804_);
lean_inc(v_infoState_803_);
lean_inc(v_messages_802_);
lean_inc(v_recordedDeps_801_);
lean_inc(v_traceState_800_);
lean_inc(v_auxDeclNGen_799_);
lean_inc(v_ngen_798_);
lean_inc(v_nextMacroScope_797_);
lean_inc(v_env_796_);
lean_dec(v___x_795_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_829_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = l_Lean_Environment_setExporting(v_env_796_, v_isExporting_789_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 5, v___x_790_);
lean_ctor_set(v___x_806_, 0, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_nextMacroScope_797_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_ngen_798_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_auxDeclNGen_799_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_traceState_800_);
lean_ctor_set(v_reuseFailAlloc_828_, 5, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_828_, 6, v_recordedDeps_801_);
lean_ctor_set(v_reuseFailAlloc_828_, 7, v_messages_802_);
lean_ctor_set(v_reuseFailAlloc_828_, 8, v_infoState_803_);
lean_ctor_set(v_reuseFailAlloc_828_, 9, v_snapshotTasks_804_);
v___x_810_ = v_reuseFailAlloc_828_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_mctx_813_; lean_object* v_zetaDeltaFVarIds_814_; lean_object* v_postponed_815_; lean_object* v_diag_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_826_; 
v___x_811_ = lean_st_ref_put(v___y_788_, v___x_810_);
v___x_812_ = lean_st_ref_take(v___y_791_);
v_mctx_813_ = lean_ctor_get(v___x_812_, 0);
v_zetaDeltaFVarIds_814_ = lean_ctor_get(v___x_812_, 2);
v_postponed_815_ = lean_ctor_get(v___x_812_, 3);
v_diag_816_ = lean_ctor_get(v___x_812_, 4);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v___x_812_, 1);
lean_dec(v_unused_827_);
v___x_818_ = v___x_812_;
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_diag_816_);
lean_inc(v_postponed_815_);
lean_inc(v_zetaDeltaFVarIds_814_);
lean_inc(v_mctx_813_);
lean_dec(v___x_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_826_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_792_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_mctx_813_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_zetaDeltaFVarIds_814_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_postponed_815_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_diag_816_);
v___x_822_ = v_reuseFailAlloc_825_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_st_ref_put(v___y_791_, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_820_);
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_788_ = stack[0].m_obj;
uint8_t v_isExporting_789_ = stack[1].m_num;
lean_object* v___x_790_ = stack[2].m_obj;
lean_object* v___y_791_ = stack[3].m_obj;
lean_object* v___x_792_ = stack[4].m_obj;
lean_object* v_a_x3f_793_ = stack[5].m_obj;
lean_object* v_res_831_;
v_res_831_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_788_, v_isExporting_789_, v___x_790_, v___y_791_, v___x_792_, v_a_x3f_793_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_832_, lean_object* v_isExporting_833_, lean_object* v___x_834_, lean_object* v___y_835_, lean_object* v___x_836_, lean_object* v_a_x3f_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_isExporting_boxed_839_; lean_object* v_res_840_; 
v_isExporting_boxed_839_ = lean_unbox(v_isExporting_833_);
v_res_840_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_832_, v_isExporting_boxed_839_, v___x_834_, v___y_835_, v___x_836_, v_a_x3f_837_);
lean_dec(v_a_x3f_837_);
lean_dec(v___y_835_);
lean_dec(v___y_832_);
return v_res_840_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_841_, uint8_t v_isExporting_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_env_849_; lean_object* v___x_850_; uint8_t v_isModule_851_; 
v___x_848_ = lean_st_ref_get(v___y_846_);
v_env_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc_ref(v_env_849_);
lean_dec(v___x_848_);
v___x_850_ = l_Lean_Environment_header(v_env_849_);
v_isModule_851_ = lean_ctor_get_uint8(v___x_850_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_850_);
if (v_isModule_851_ == 0)
{
lean_object* v___x_852_; 
lean_dec_ref(v_env_849_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
v___x_852_ = lean_apply_5(v_x_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_852_;
}
else
{
uint8_t v_isExporting_853_; 
v_isExporting_853_ = lean_ctor_get_uint8(v_env_849_, sizeof(void*)*13);
lean_dec_ref(v_env_849_);
if (v_isExporting_842_ == 0)
{
if (v_isExporting_853_ == 0)
{
lean_object* v___x_920_; 
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
v___x_920_ = lean_apply_5(v_x_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_920_;
}
else
{
goto v___jp_854_;
}
}
else
{
if (v_isExporting_853_ == 0)
{
goto v___jp_854_;
}
else
{
lean_object* v___x_921_; 
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
v___x_921_ = lean_apply_5(v_x_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
return v___x_921_;
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v_env_856_; lean_object* v_nextMacroScope_857_; lean_object* v_ngen_858_; lean_object* v_auxDeclNGen_859_; lean_object* v_traceState_860_; lean_object* v_recordedDeps_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_918_; 
v___x_855_ = lean_st_ref_take(v___y_846_);
v_env_856_ = lean_ctor_get(v___x_855_, 0);
v_nextMacroScope_857_ = lean_ctor_get(v___x_855_, 1);
v_ngen_858_ = lean_ctor_get(v___x_855_, 2);
v_auxDeclNGen_859_ = lean_ctor_get(v___x_855_, 3);
v_traceState_860_ = lean_ctor_get(v___x_855_, 4);
v_recordedDeps_861_ = lean_ctor_get(v___x_855_, 6);
v_messages_862_ = lean_ctor_get(v___x_855_, 7);
v_infoState_863_ = lean_ctor_get(v___x_855_, 8);
v_snapshotTasks_864_ = lean_ctor_get(v___x_855_, 9);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_855_, 5);
lean_dec(v_unused_919_);
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_918_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_recordedDeps_861_);
lean_inc(v_traceState_860_);
lean_inc(v_auxDeclNGen_859_);
lean_inc(v_ngen_858_);
lean_inc(v_nextMacroScope_857_);
lean_inc(v_env_856_);
lean_dec(v___x_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_918_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = l_Lean_Environment_setExporting(v_env_856_, v_isExporting_842_);
v___x_869_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 5, v___x_869_);
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_nextMacroScope_857_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_ngen_858_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_auxDeclNGen_859_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_traceState_860_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_917_, 6, v_recordedDeps_861_);
lean_ctor_set(v_reuseFailAlloc_917_, 7, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_917_, 8, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_917_, 9, v_snapshotTasks_864_);
v___x_871_ = v_reuseFailAlloc_917_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_mctx_874_; lean_object* v_zetaDeltaFVarIds_875_; lean_object* v_postponed_876_; lean_object* v_diag_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_915_; 
v___x_872_ = lean_st_ref_put(v___y_846_, v___x_871_);
v___x_873_ = lean_st_ref_take(v___y_844_);
v_mctx_874_ = lean_ctor_get(v___x_873_, 0);
v_zetaDeltaFVarIds_875_ = lean_ctor_get(v___x_873_, 2);
v_postponed_876_ = lean_ctor_get(v___x_873_, 3);
v_diag_877_ = lean_ctor_get(v___x_873_, 4);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v___x_873_, 1);
lean_dec(v_unused_916_);
v___x_879_ = v___x_873_;
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_diag_877_);
lean_inc(v_postponed_876_);
lean_inc(v_zetaDeltaFVarIds_875_);
lean_inc(v_mctx_874_);
lean_dec(v___x_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_mctx_874_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_zetaDeltaFVarIds_875_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_postponed_876_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_diag_877_);
v___x_883_ = v_reuseFailAlloc_914_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v_r_885_; 
v___x_884_ = lean_st_ref_put(v___y_844_, v___x_883_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
v_r_885_ = lean_apply_5(v_x_841_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, lean_box(0));
if (lean_obj_tag(v_r_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_902_; 
v_a_886_ = lean_ctor_get(v_r_885_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_r_885_);
if (v_isSharedCheck_902_ == 0)
{
v___x_888_ = v_r_885_;
v_isShared_889_ = v_isSharedCheck_902_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v_r_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_902_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
lean_inc(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_901_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v___x_892_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_846_, v_isExporting_853_, v___x_869_, v___y_844_, v___x_881_, v___x_891_);
lean_dec_ref(v___x_891_);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_900_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_a_886_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_886_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_903_ = lean_ctor_get(v_r_885_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v_r_885_, 1);
v___x_904_ = lean_box(0);
v___x_905_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_846_, v_isExporting_853_, v___x_869_, v___y_844_, v___x_881_, v___x_904_);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_913_);
v___x_907_ = v___x_905_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_905_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 1);
lean_ctor_set(v___x_907_, 0, v_a_903_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_903_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_841_ = stack[0].m_obj;
uint8_t v_isExporting_842_ = stack[1].m_num;
lean_object* v___y_843_ = stack[2].m_obj;
lean_object* v___y_844_ = stack[3].m_obj;
lean_object* v___y_845_ = stack[4].m_obj;
lean_object* v___y_846_ = stack[5].m_obj;
lean_object* v_res_922_;
v_res_922_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_841_, v_isExporting_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_923_, lean_object* v_isExporting_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_isExporting_boxed_930_; lean_object* v_res_931_; 
v_isExporting_boxed_930_ = lean_unbox(v_isExporting_924_);
v_res_931_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_923_, v_isExporting_boxed_930_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_931_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_932_, uint8_t v_when_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
if (v_when_933_ == 0)
{
lean_object* v___x_939_; 
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
v___x_939_ = lean_apply_5(v_x_932_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
return v___x_939_;
}
else
{
uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_940_ = 0;
v___x_941_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_932_, v___x_940_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_941_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_932_ = stack[0].m_obj;
uint8_t v_when_933_ = stack[1].m_num;
lean_object* v___y_934_ = stack[2].m_obj;
lean_object* v___y_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v___y_937_ = stack[5].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_932_, v_when_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_943_, lean_object* v_when_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v_when_boxed_950_; lean_object* v_res_951_; 
v_when_boxed_950_ = lean_unbox(v_when_944_);
v_res_951_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_943_, v_when_boxed_950_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_951_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_952_, lean_object* v_projDecls_953_, lean_object* v___x_954_, lean_object* v___x_955_, uint8_t v_instImplicit_956_, lean_object* v___x_957_, lean_object* v_params_958_, lean_object* v_self_959_, lean_object* v_a_960_, lean_object* v___x_961_, lean_object* v_n_962_, lean_object* v___x_963_, uint8_t v_a_964_, lean_object* v_a_965_, lean_object* v_b_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_972_; 
v___x_972_ = lean_nat_dec_lt(v_a_965_, v_upperBound_952_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec(v_a_965_);
lean_dec(v___x_963_);
lean_dec(v_n_962_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v_self_959_);
lean_dec_ref(v_params_958_);
lean_dec(v___x_957_);
lean_dec(v___x_955_);
lean_dec_ref(v___x_954_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_b_966_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; lean_object* v_ref_975_; lean_object* v_projName_976_; lean_object* v_paramInfoOverrides_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___f_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___y_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_974_ = lean_array_fget_borrowed(v_projDecls_953_, v_a_965_);
v_ref_975_ = lean_ctor_get(v___x_974_, 0);
v_projName_976_ = lean_ctor_get(v___x_974_, 1);
v_paramInfoOverrides_977_ = lean_ctor_get(v___x_974_, 2);
v___x_978_ = lean_box(v_instImplicit_956_);
v___x_979_ = lean_box(v___x_972_);
v___x_980_ = lean_box(v_a_964_);
lean_inc(v___x_963_);
lean_inc_n(v_ref_975_, 2);
lean_inc_n(v_n_962_, 2);
lean_inc(v_paramInfoOverrides_977_);
lean_inc_ref(v___x_961_);
lean_inc_ref(v_a_960_);
lean_inc_ref(v_b_966_);
lean_inc_ref(v_self_959_);
lean_inc_ref(v_params_958_);
lean_inc(v___x_957_);
lean_inc(v_a_965_);
lean_inc(v___x_955_);
lean_inc_n(v_projName_976_, 2);
lean_inc_ref(v___x_954_);
v___f_981_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_981_, 0, v___x_954_);
lean_closure_set(v___f_981_, 1, v_projName_976_);
lean_closure_set(v___f_981_, 2, v___x_955_);
lean_closure_set(v___f_981_, 3, v_a_965_);
lean_closure_set(v___f_981_, 4, v___x_978_);
lean_closure_set(v___f_981_, 5, v___x_957_);
lean_closure_set(v___f_981_, 6, v_params_958_);
lean_closure_set(v___f_981_, 7, v_self_959_);
lean_closure_set(v___f_981_, 8, v_b_966_);
lean_closure_set(v___f_981_, 9, v___x_979_);
lean_closure_set(v___f_981_, 10, v_a_960_);
lean_closure_set(v___f_981_, 11, v___x_961_);
lean_closure_set(v___f_981_, 12, v_paramInfoOverrides_977_);
lean_closure_set(v___f_981_, 13, v_n_962_);
lean_closure_set(v___f_981_, 14, v_ref_975_);
lean_closure_set(v___f_981_, 15, v___x_963_);
lean_closure_set(v___f_981_, 16, v___x_980_);
v___x_982_ = l_Lean_Expr_isForall(v_b_966_);
lean_dec_ref(v_b_966_);
v___x_983_ = lean_box(v___x_982_);
v___y_984_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_984_, 0, v___x_983_);
lean_closure_set(v___y_984_, 1, v_projName_976_);
lean_closure_set(v___y_984_, 2, v_n_962_);
lean_closure_set(v___y_984_, 3, v_ref_975_);
lean_closure_set(v___y_984_, 4, v___f_981_);
v___x_985_ = l_Lean_isPrivateName(v_projName_976_);
v___x_986_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_984_, v___x_985_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_nat_add(v_a_965_, v___x_988_);
lean_dec(v_a_965_);
v_a_965_ = v___x_989_;
v_b_966_ = v_a_987_;
goto _start;
}
else
{
lean_dec(v_a_965_);
lean_dec(v___x_963_);
lean_dec(v_n_962_);
lean_dec_ref(v___x_961_);
lean_dec_ref(v_a_960_);
lean_dec_ref(v_self_959_);
lean_dec_ref(v_params_958_);
lean_dec(v___x_957_);
lean_dec(v___x_955_);
lean_dec_ref(v___x_954_);
return v___x_986_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_952_ = stack[0].m_obj;
lean_object* v_projDecls_953_ = stack[1].m_obj;
lean_object* v___x_954_ = stack[2].m_obj;
lean_object* v___x_955_ = stack[3].m_obj;
uint8_t v_instImplicit_956_ = stack[4].m_num;
lean_object* v___x_957_ = stack[5].m_obj;
lean_object* v_params_958_ = stack[6].m_obj;
lean_object* v_self_959_ = stack[7].m_obj;
lean_object* v_a_960_ = stack[8].m_obj;
lean_object* v___x_961_ = stack[9].m_obj;
lean_object* v_n_962_ = stack[10].m_obj;
lean_object* v___x_963_ = stack[11].m_obj;
uint8_t v_a_964_ = stack[12].m_num;
lean_object* v_a_965_ = stack[13].m_obj;
lean_object* v_b_966_ = stack[14].m_obj;
lean_object* v___y_967_ = stack[15].m_obj;
lean_object* v___y_968_ = stack[16].m_obj;
lean_object* v___y_969_ = stack[17].m_obj;
lean_object* v___y_970_ = stack[18].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_952_, v_projDecls_953_, v___x_954_, v___x_955_, v_instImplicit_956_, v___x_957_, v_params_958_, v_self_959_, v_a_960_, v___x_961_, v_n_962_, v___x_963_, v_a_964_, v_a_965_, v_b_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_992_ = _args[0];
lean_object* v_projDecls_993_ = _args[1];
lean_object* v___x_994_ = _args[2];
lean_object* v___x_995_ = _args[3];
lean_object* v_instImplicit_996_ = _args[4];
lean_object* v___x_997_ = _args[5];
lean_object* v_params_998_ = _args[6];
lean_object* v_self_999_ = _args[7];
lean_object* v_a_1000_ = _args[8];
lean_object* v___x_1001_ = _args[9];
lean_object* v_n_1002_ = _args[10];
lean_object* v___x_1003_ = _args[11];
lean_object* v_a_1004_ = _args[12];
lean_object* v_a_1005_ = _args[13];
lean_object* v_b_1006_ = _args[14];
lean_object* v___y_1007_ = _args[15];
lean_object* v___y_1008_ = _args[16];
lean_object* v___y_1009_ = _args[17];
lean_object* v___y_1010_ = _args[18];
lean_object* v___y_1011_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1012_; uint8_t v_a_18479__boxed_1013_; lean_object* v_res_1014_; 
v_instImplicit_boxed_1012_ = lean_unbox(v_instImplicit_996_);
v_a_18479__boxed_1013_ = lean_unbox(v_a_1004_);
v_res_1014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_992_, v_projDecls_993_, v___x_994_, v___x_995_, v_instImplicit_boxed_1012_, v___x_997_, v_params_998_, v_self_999_, v_a_1000_, v___x_1001_, v_n_1002_, v___x_1003_, v_a_18479__boxed_1013_, v_a_1005_, v_b_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_projDecls_993_);
lean_dec(v_upperBound_992_);
return v_res_1014_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_1015_, lean_object* v_as_1016_, size_t v_sz_1017_, size_t v_i_1018_, lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_a_1025_; uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_lt(v_i_1018_, v_sz_1017_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_b_1019_);
return v___x_1030_;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1031_ = lean_array_uget_borrowed(v_as_1016_, v_i_1018_);
v___x_1032_ = l_Lean_Expr_fvarId_x21(v_a_1031_);
lean_inc(v___x_1032_);
v___x_1033_ = l_Lean_FVarId_getDecl___redArg(v___x_1032_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; uint8_t v___y_1036_; uint8_t v___x_1039_; uint8_t v___x_1040_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1039_ = l_Lean_LocalDecl_binderInfo(v_a_1034_);
v___x_1040_ = l_Lean_BinderInfo_isInstImplicit(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = l_Lean_LocalDecl_type(v_a_1034_);
lean_dec(v_a_1034_);
v___x_1043_ = l_Lean_Expr_isOutParam(v___x_1042_);
lean_dec_ref(v___x_1042_);
if (v___x_1043_ == 0)
{
uint8_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = 0;
v___x_1045_ = l_Lean_LocalContext_setBinderInfo(v_b_1019_, v___x_1032_, v___x_1044_);
v_a_1025_ = v___x_1045_;
goto v___jp_1024_;
}
else
{
goto v___jp_1041_;
}
}
else
{
lean_dec(v_a_1034_);
goto v___jp_1041_;
}
v___jp_1035_:
{
if (v___y_1036_ == 0)
{
lean_dec(v___x_1032_);
v_a_1025_ = v_b_1019_;
goto v___jp_1024_;
}
else
{
uint8_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = 1;
v___x_1038_ = l_Lean_LocalContext_setBinderInfo(v_b_1019_, v___x_1032_, v___x_1037_);
v_a_1025_ = v___x_1038_;
goto v___jp_1024_;
}
}
v___jp_1041_:
{
if (v___x_1040_ == 0)
{
v___y_1036_ = v___x_1040_;
goto v___jp_1035_;
}
else
{
v___y_1036_ = v_instImplicit_1015_;
goto v___jp_1035_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec(v___x_1032_);
lean_dec_ref(v_b_1019_);
v_a_1046_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1033_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1033_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
v___jp_1024_:
{
size_t v___x_1026_; size_t v___x_1027_; 
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1018_, v___x_1026_);
v_i_1018_ = v___x_1027_;
v_b_1019_ = v_a_1025_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_instImplicit_1015_ = stack[0].m_num;
lean_object* v_as_1016_ = stack[1].m_obj;
size_t v_sz_1017_ = stack[2].m_num;
size_t v_i_1018_ = stack[3].m_num;
lean_object* v_b_1019_ = stack[4].m_obj;
lean_object* v___y_1020_ = stack[5].m_obj;
lean_object* v___y_1021_ = stack[6].m_obj;
lean_object* v___y_1022_ = stack[7].m_obj;
lean_object* v_res_1054_;
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1015_, v_as_1016_, v_sz_1017_, v_i_1018_, v_b_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
stack->m_obj
 = v_res_1054_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1055_, lean_object* v_as_1056_, lean_object* v_sz_1057_, lean_object* v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v_instImplicit_boxed_1064_; size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_instImplicit_boxed_1064_ = lean_unbox(v_instImplicit_1055_);
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1057_);
lean_dec(v_sz_1057_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1058_);
lean_dec(v_i_1058_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1064_, v_as_1056_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1067_;
}
}
lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1068_, uint8_t v_instImplicit_1069_, lean_object* v_projDecls_1070_, lean_object* v_toConstantVal_1071_, lean_object* v_numParams_1072_, lean_object* v___x_1073_, lean_object* v_n_1074_, lean_object* v_levelParams_1075_, uint8_t v_a_1076_, lean_object* v_ctorType_1077_, lean_object* v_self_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_lctx_1084_; lean_object* v___x_1085_; size_t v_sz_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v_lctx_1084_ = lean_ctor_get(v___y_1079_, 2);
lean_inc_ref(v_self_1078_);
lean_inc_ref(v_params_1068_);
v___x_1085_ = lean_array_push(v_params_1068_, v_self_1078_);
v_sz_1086_ = lean_array_size(v_params_1068_);
v___x_1087_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1084_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1069_, v_params_1068_, v_sz_1086_, v___x_1087_, v_lctx_1084_, v___y_1079_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = lean_array_get_size(v_projDecls_1070_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1090_, v_projDecls_1070_, v_toConstantVal_1071_, v_numParams_1072_, v_instImplicit_1069_, v___x_1073_, v_params_1068_, v_self_1078_, v_a_1089_, v___x_1085_, v_n_1074_, v_levelParams_1075_, v_a_1076_, v___x_1091_, v_ctorType_1077_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1101_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(0);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1092_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_self_1078_);
lean_dec_ref(v_ctorType_1077_);
lean_dec(v_levelParams_1075_);
lean_dec(v_n_1074_);
lean_dec(v___x_1073_);
lean_dec(v_numParams_1072_);
lean_dec_ref(v_toConstantVal_1071_);
lean_dec_ref(v_params_1068_);
v_a_1110_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1088_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1088_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkProjections___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1068_ = stack[0].m_obj;
uint8_t v_instImplicit_1069_ = stack[1].m_num;
lean_object* v_projDecls_1070_ = stack[2].m_obj;
lean_object* v_toConstantVal_1071_ = stack[3].m_obj;
lean_object* v_numParams_1072_ = stack[4].m_obj;
lean_object* v___x_1073_ = stack[5].m_obj;
lean_object* v_n_1074_ = stack[6].m_obj;
lean_object* v_levelParams_1075_ = stack[7].m_obj;
uint8_t v_a_1076_ = stack[8].m_num;
lean_object* v_ctorType_1077_ = stack[9].m_obj;
lean_object* v_self_1078_ = stack[10].m_obj;
lean_object* v___y_1079_ = stack[11].m_obj;
lean_object* v___y_1080_ = stack[12].m_obj;
lean_object* v___y_1081_ = stack[13].m_obj;
lean_object* v___y_1082_ = stack[14].m_obj;
lean_object* v_res_1118_;
v_res_1118_ = l_Lean_Meta_mkProjections___lam__0(v_params_1068_, v_instImplicit_1069_, v_projDecls_1070_, v_toConstantVal_1071_, v_numParams_1072_, v___x_1073_, v_n_1074_, v_levelParams_1075_, v_a_1076_, v_ctorType_1077_, v_self_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
stack->m_obj
 = v_res_1118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1119_, lean_object* v_instImplicit_1120_, lean_object* v_projDecls_1121_, lean_object* v_toConstantVal_1122_, lean_object* v_numParams_1123_, lean_object* v___x_1124_, lean_object* v_n_1125_, lean_object* v_levelParams_1126_, lean_object* v_a_1127_, lean_object* v_ctorType_1128_, lean_object* v_self_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
uint8_t v_instImplicit_boxed_1135_; uint8_t v_a_18703__boxed_1136_; lean_object* v_res_1137_; 
v_instImplicit_boxed_1135_ = lean_unbox(v_instImplicit_1120_);
v_a_18703__boxed_1136_ = lean_unbox(v_a_1127_);
v_res_1137_ = l_Lean_Meta_mkProjections___lam__0(v_params_1119_, v_instImplicit_boxed_1135_, v_projDecls_1121_, v_toConstantVal_1122_, v_numParams_1123_, v___x_1124_, v_n_1125_, v_levelParams_1126_, v_a_18703__boxed_1136_, v_ctorType_1128_, v_self_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_projDecls_1121_);
return v_res_1137_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1147_, lean_object* v_projDecls_1148_, lean_object* v_toConstantVal_1149_, lean_object* v_numParams_1150_, lean_object* v___x_1151_, lean_object* v_n_1152_, lean_object* v_levelParams_1153_, uint8_t v_a_1154_, lean_object* v_params_1155_, lean_object* v_ctorType_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1173_ = lean_box(v_instImplicit_1147_);
v___x_1174_ = lean_box(v_a_1154_);
lean_inc(v_n_1152_);
lean_inc(v___x_1151_);
lean_inc(v_numParams_1150_);
lean_inc_ref(v_params_1155_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1175_, 0, v_params_1155_);
lean_closure_set(v___f_1175_, 1, v___x_1173_);
lean_closure_set(v___f_1175_, 2, v_projDecls_1148_);
lean_closure_set(v___f_1175_, 3, v_toConstantVal_1149_);
lean_closure_set(v___f_1175_, 4, v_numParams_1150_);
lean_closure_set(v___f_1175_, 5, v___x_1151_);
lean_closure_set(v___f_1175_, 6, v_n_1152_);
lean_closure_set(v___f_1175_, 7, v_levelParams_1153_);
lean_closure_set(v___f_1175_, 8, v___x_1174_);
lean_closure_set(v___f_1175_, 9, v_ctorType_1156_);
v___x_1181_ = lean_array_get_size(v_params_1155_);
v___x_1182_ = lean_nat_dec_eq(v___x_1181_, v_numParams_1150_);
lean_dec(v_numParams_1150_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v___f_1175_);
lean_dec_ref(v_params_1155_);
lean_dec(v___x_1151_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1184_ = l_Lean_MessageData_ofConstName(v_n_1152_, v___x_1182_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1187_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
return v___x_1188_;
}
else
{
goto v___jp_1176_;
}
v___jp_1162_:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1171_ = 0;
v___x_1172_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1170_, v___y_1169_, v___y_1164_, v___y_1168_, v___x_1171_, v___y_1165_, v___y_1166_, v___y_1163_, v___y_1167_);
return v___x_1172_;
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_Expr_const___override(v_n_1152_, v___x_1151_);
v___x_1178_ = l_Lean_mkAppN(v___x_1177_, v_params_1155_);
lean_dec_ref(v_params_1155_);
if (v_instImplicit_1147_ == 0)
{
uint8_t v___x_1179_; 
v___x_1179_ = 0;
v___y_1163_ = v___y_1159_;
v___y_1164_ = v___x_1178_;
v___y_1165_ = v___y_1157_;
v___y_1166_ = v___y_1158_;
v___y_1167_ = v___y_1160_;
v___y_1168_ = v___f_1175_;
v___y_1169_ = v___x_1179_;
goto v___jp_1162_;
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = 3;
v___y_1163_ = v___y_1159_;
v___y_1164_ = v___x_1178_;
v___y_1165_ = v___y_1157_;
v___y_1166_ = v___y_1158_;
v___y_1167_ = v___y_1160_;
v___y_1168_ = v___f_1175_;
v___y_1169_ = v___x_1180_;
goto v___jp_1162_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkProjections___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_instImplicit_1147_ = stack[0].m_num;
lean_object* v_projDecls_1148_ = stack[1].m_obj;
lean_object* v_toConstantVal_1149_ = stack[2].m_obj;
lean_object* v_numParams_1150_ = stack[3].m_obj;
lean_object* v___x_1151_ = stack[4].m_obj;
lean_object* v_n_1152_ = stack[5].m_obj;
lean_object* v_levelParams_1153_ = stack[6].m_obj;
uint8_t v_a_1154_ = stack[7].m_num;
lean_object* v_params_1155_ = stack[8].m_obj;
lean_object* v_ctorType_1156_ = stack[9].m_obj;
lean_object* v___y_1157_ = stack[10].m_obj;
lean_object* v___y_1158_ = stack[11].m_obj;
lean_object* v___y_1159_ = stack[12].m_obj;
lean_object* v___y_1160_ = stack[13].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_1147_, v_projDecls_1148_, v_toConstantVal_1149_, v_numParams_1150_, v___x_1151_, v_n_1152_, v_levelParams_1153_, v_a_1154_, v_params_1155_, v_ctorType_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1190_, lean_object* v_projDecls_1191_, lean_object* v_toConstantVal_1192_, lean_object* v_numParams_1193_, lean_object* v___x_1194_, lean_object* v_n_1195_, lean_object* v_levelParams_1196_, lean_object* v_a_1197_, lean_object* v_params_1198_, lean_object* v_ctorType_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_instImplicit_boxed_1205_; uint8_t v_a_18853__boxed_1206_; lean_object* v_res_1207_; 
v_instImplicit_boxed_1205_ = lean_unbox(v_instImplicit_1190_);
v_a_18853__boxed_1206_ = lean_unbox(v_a_1197_);
v_res_1207_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1205_, v_projDecls_1191_, v_toConstantVal_1192_, v_numParams_1193_, v___x_1194_, v_n_1195_, v_levelParams_1196_, v_a_18853__boxed_1206_, v_params_1198_, v_ctorType_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
if (lean_obj_tag(v_a_1208_) == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = l_List_reverse___redArg(v_a_1209_);
return v___x_1210_;
}
else
{
lean_object* v_head_1211_; lean_object* v_tail_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
v_head_1211_ = lean_ctor_get(v_a_1208_, 0);
v_tail_1212_ = lean_ctor_get(v_a_1208_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_a_1208_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1214_ = v_a_1208_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_tail_1212_);
lean_inc(v_head_1211_);
lean_dec(v_a_1208_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = l_Lean_mkLevelParam(v_head_1211_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_a_1209_);
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_a_1209_);
v___x_1218_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v_a_1208_ = v_tail_1212_;
v_a_1209_ = v___x_1218_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_instMonadEIO___redArg();
return v___x_1222_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_toApplicative_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1296_; 
v___x_1233_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1234_ = l_StateRefT_x27_instMonad___redArg(v___x_1233_);
v_toApplicative_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1234_, 1);
lean_dec(v_unused_1297_);
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1296_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_toApplicative_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1296_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_toFunctor_1239_; lean_object* v_toSeq_1240_; lean_object* v_toSeqLeft_1241_; lean_object* v_toSeqRight_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1294_; 
v_toFunctor_1239_ = lean_ctor_get(v_toApplicative_1235_, 0);
v_toSeq_1240_ = lean_ctor_get(v_toApplicative_1235_, 2);
v_toSeqLeft_1241_ = lean_ctor_get(v_toApplicative_1235_, 3);
v_toSeqRight_1242_ = lean_ctor_get(v_toApplicative_1235_, 4);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_toApplicative_1235_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_toApplicative_1235_, 1);
lean_dec(v_unused_1295_);
v___x_1244_ = v_toApplicative_1235_;
v_isShared_1245_ = v_isSharedCheck_1294_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_toSeqRight_1242_);
lean_inc(v_toSeqLeft_1241_);
lean_inc(v_toSeq_1240_);
lean_inc(v_toFunctor_1239_);
lean_dec(v_toApplicative_1235_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1294_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1255_; 
v___f_1246_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1247_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1239_);
v___f_1248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1248_, 0, v_toFunctor_1239_);
v___f_1249_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1249_, 0, v_toFunctor_1239_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___f_1248_);
lean_ctor_set(v___x_1250_, 1, v___f_1249_);
v___f_1251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1251_, 0, v_toSeqRight_1242_);
v___f_1252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1252_, 0, v_toSeqLeft_1241_);
v___f_1253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1253_, 0, v_toSeq_1240_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 4, v___f_1251_);
lean_ctor_set(v___x_1244_, 3, v___f_1252_);
lean_ctor_set(v___x_1244_, 2, v___f_1253_);
lean_ctor_set(v___x_1244_, 1, v___f_1246_);
lean_ctor_set(v___x_1244_, 0, v___x_1250_);
v___x_1255_ = v___x_1244_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___f_1246_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v___f_1253_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v___f_1252_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v___f_1251_);
v___x_1255_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___f_1247_);
lean_ctor_set(v___x_1237_, 0, v___x_1255_);
v___x_1257_ = v___x_1237_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___f_1247_);
v___x_1257_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v_toApplicative_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1290_; 
v___x_1258_ = l_StateRefT_x27_instMonad___redArg(v___x_1257_);
v_toApplicative_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1258_, 1);
lean_dec(v_unused_1291_);
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1290_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_toApplicative_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1290_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_toFunctor_1263_; lean_object* v_toSeq_1264_; lean_object* v_toSeqLeft_1265_; lean_object* v_toSeqRight_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1288_; 
v_toFunctor_1263_ = lean_ctor_get(v_toApplicative_1259_, 0);
v_toSeq_1264_ = lean_ctor_get(v_toApplicative_1259_, 2);
v_toSeqLeft_1265_ = lean_ctor_get(v_toApplicative_1259_, 3);
v_toSeqRight_1266_ = lean_ctor_get(v_toApplicative_1259_, 4);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_toApplicative_1259_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_toApplicative_1259_, 1);
lean_dec(v_unused_1289_);
v___x_1268_ = v_toApplicative_1259_;
v_isShared_1269_ = v_isSharedCheck_1288_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_toSeqRight_1266_);
lean_inc(v_toSeqLeft_1265_);
lean_inc(v_toSeq_1264_);
lean_inc(v_toFunctor_1263_);
lean_dec(v_toApplicative_1259_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1288_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___x_1274_; lean_object* v___f_1275_; lean_object* v___f_1276_; lean_object* v___f_1277_; lean_object* v___x_1279_; 
v___f_1270_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1271_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1263_);
v___f_1272_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1272_, 0, v_toFunctor_1263_);
v___f_1273_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1273_, 0, v_toFunctor_1263_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___f_1272_);
lean_ctor_set(v___x_1274_, 1, v___f_1273_);
v___f_1275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1275_, 0, v_toSeqRight_1266_);
v___f_1276_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1276_, 0, v_toSeqLeft_1265_);
v___f_1277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1277_, 0, v_toSeq_1264_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___f_1275_);
lean_ctor_set(v___x_1268_, 3, v___f_1276_);
lean_ctor_set(v___x_1268_, 2, v___f_1277_);
lean_ctor_set(v___x_1268_, 1, v___f_1270_);
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1279_ = v___x_1268_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___f_1270_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v___f_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v___f_1276_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v___f_1275_);
v___x_1279_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___f_1271_);
lean_ctor_set(v___x_1261_, 0, v___x_1279_);
v___x_1281_ = v___x_1261_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___f_1271_);
v___x_1281_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_13115__overap_1284_; lean_object* v___x_1285_; 
v___x_1282_ = lean_box(0);
v___x_1283_ = l_instInhabitedOfMonad___redArg(v___x_1281_, v___x_1282_);
v___x_13115__overap_1284_ = lean_panic_fn_borrowed(v___x_1283_, v_msg_1227_);
lean_dec(v___x_1283_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
v___x_1285_ = lean_apply_5(v___x_13115__overap_1284_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, lean_box(0));
return v___x_1285_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1227_ = stack[0].m_obj;
lean_object* v___y_1228_ = stack[1].m_obj;
lean_object* v___y_1229_ = stack[2].m_obj;
lean_object* v___y_1230_ = stack[3].m_obj;
lean_object* v___y_1231_ = stack[4].m_obj;
lean_object* v_res_1298_;
v_res_1298_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
return v_res_1305_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1312_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1313_ = lean_unsigned_to_nat(11u);
v___x_1314_ = lean_unsigned_to_nat(122u);
v___x_1315_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1316_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1317_ = l_mkPanicMessageWithDecl(v___x_1316_, v___x_1315_, v___x_1314_, v___x_1313_, v___x_1312_);
return v___x_1317_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1332_; lean_object* v_env_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = lean_st_ref_get(v___y_1322_);
v_env_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_ref(v_env_1333_);
lean_dec(v___x_1332_);
v___x_1334_ = 0;
lean_inc(v_constName_1318_);
v___x_1335_ = l_Lean_Environment_findAsync_x3f(v_env_1333_, v_constName_1318_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 1)
{
lean_object* v_val_1336_; uint8_t v_kind_1337_; 
v_val_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_kind_1337_ = lean_ctor_get_uint8(v_val_1336_, sizeof(void*)*3);
if (v_kind_1337_ == 6)
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1336_);
if (lean_obj_tag(v___x_1338_) == 6)
{
lean_object* v_val_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_constName_1318_);
v_val_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_val_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set_tag(v___x_1341_, 0);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_val_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v___x_1338_);
v___x_1347_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1348_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1347_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1357_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
if (lean_obj_tag(v_a_1349_) == 0)
{
lean_del_object(v___x_1351_);
goto v___jp_1324_;
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1355_; 
lean_dec(v_constName_1318_);
v_val_1353_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_a_1349_, 1);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_val_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_val_1353_);
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
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_constName_1318_);
v_a_1358_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1348_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1348_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_dec(v_val_1336_);
goto v___jp_1324_;
}
}
else
{
lean_dec(v___x_1335_);
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1326_ = 0;
v___x_1327_ = l_Lean_MessageData_ofConstName(v_constName_1318_, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1325_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1330_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
return v___x_1331_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1318_ = stack[0].m_obj;
lean_object* v___y_1319_ = stack[1].m_obj;
lean_object* v___y_1320_ = stack[2].m_obj;
lean_object* v___y_1321_ = stack[3].m_obj;
lean_object* v___y_1322_ = stack[4].m_obj;
lean_object* v_res_1366_;
v_res_1366_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
stack->m_obj
 = v_res_1366_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v_env_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_st_ref_get(v___y_1381_);
v_env_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_env_1384_);
lean_dec(v___x_1383_);
lean_inc(v_constName_1377_);
v___x_1385_ = l_Lean_isInductiveCore_x3f(v_env_1384_, v_constName_1377_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1386_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1387_ = 0;
v___x_1388_ = l_Lean_MessageData_ofConstName(v_constName_1377_, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1386_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1391_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1392_;
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_constName_1377_);
v_val_1393_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1385_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_val_1393_);
lean_dec(v___x_1385_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 0);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_val_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1377_ = stack[0].m_obj;
lean_object* v___y_1378_ = stack[1].m_obj;
lean_object* v___y_1379_ = stack[2].m_obj;
lean_object* v___y_1380_ = stack[3].m_obj;
lean_object* v___y_1381_ = stack[4].m_obj;
lean_object* v_res_1401_;
v_res_1401_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
stack->m_obj
 = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1408_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1415_, lean_object* v___x_1416_, uint8_t v_instImplicit_1417_, lean_object* v_projDecls_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
lean_inc(v_n_1415_);
v___x_1424_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1415_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1466_ = l_Lean_InductiveVal_numCtors(v_a_1425_);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_dec_eq(v___x_1466_, v___x_1467_);
lean_dec(v___x_1466_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec(v_a_1425_);
lean_dec_ref(v_projDecls_1418_);
v___x_1469_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1470_ = l_Lean_MessageData_ofConstName(v_n_1415_, v___x_1468_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1473_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v___x_1474_;
}
else
{
v___y_1427_ = v___y_1419_;
v___y_1428_ = v___y_1420_;
v___y_1429_ = v___y_1421_;
v___y_1430_ = v___y_1422_;
goto v___jp_1426_;
}
v___jp_1426_:
{
lean_object* v_toConstantVal_1431_; lean_object* v_numParams_1432_; lean_object* v_ctors_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_toConstantVal_1431_ = lean_ctor_get(v_a_1425_, 0);
lean_inc_ref(v_toConstantVal_1431_);
v_numParams_1432_ = lean_ctor_get(v_a_1425_, 1);
lean_inc(v_numParams_1432_);
v_ctors_1433_ = lean_ctor_get(v_a_1425_, 4);
lean_inc(v_ctors_1433_);
lean_dec(v_a_1425_);
v___x_1434_ = l_List_head_x21___redArg(v___x_1416_, v_ctors_1433_);
lean_dec(v_ctors_1433_);
v___x_1435_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1434_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v_levelParams_1437_; lean_object* v_type_1438_; lean_object* v___x_1439_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_levelParams_1437_ = lean_ctor_get(v_toConstantVal_1431_, 1);
lean_inc(v_levelParams_1437_);
v_type_1438_ = lean_ctor_get(v_toConstantVal_1431_, 2);
lean_inc_ref(v_type_1438_);
lean_dec_ref(v_toConstantVal_1431_);
v___x_1439_ = l_Lean_Meta_isPropFormerType(v_type_1438_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_toConstantVal_1440_; lean_object* v_a_1441_; lean_object* v_type_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v_toConstantVal_1440_ = lean_ctor_get(v_a_1436_, 0);
lean_inc_ref(v_toConstantVal_1440_);
lean_dec(v_a_1436_);
v_a_1441_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1439_, 1);
v_type_1442_ = lean_ctor_get(v_toConstantVal_1440_, 2);
lean_inc_ref(v_type_1442_);
v___x_1443_ = lean_box(0);
lean_inc(v_levelParams_1437_);
v___x_1444_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1437_, v___x_1443_);
v___x_1445_ = lean_box(v_instImplicit_1417_);
lean_inc(v_numParams_1432_);
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1446_, 0, v___x_1445_);
lean_closure_set(v___f_1446_, 1, v_projDecls_1418_);
lean_closure_set(v___f_1446_, 2, v_toConstantVal_1440_);
lean_closure_set(v___f_1446_, 3, v_numParams_1432_);
lean_closure_set(v___f_1446_, 4, v___x_1444_);
lean_closure_set(v___f_1446_, 5, v_n_1415_);
lean_closure_set(v___f_1446_, 6, v_levelParams_1437_);
lean_closure_set(v___f_1446_, 7, v_a_1441_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_numParams_1432_);
v___x_1448_ = 0;
v___x_1449_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1442_, v___x_1447_, v___f_1446_, v___x_1448_, v___x_1448_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_levelParams_1437_);
lean_dec(v_a_1436_);
lean_dec(v_numParams_1432_);
lean_dec_ref(v_projDecls_1418_);
lean_dec(v_n_1415_);
v_a_1450_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1439_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1439_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_numParams_1432_);
lean_dec_ref(v_toConstantVal_1431_);
lean_dec_ref(v_projDecls_1418_);
lean_dec(v_n_1415_);
v_a_1458_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1435_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1435_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v_projDecls_1418_);
lean_dec(v_n_1415_);
v_a_1475_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1424_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1424_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkProjections___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1415_ = stack[0].m_obj;
lean_object* v___x_1416_ = stack[1].m_obj;
uint8_t v_instImplicit_1417_ = stack[2].m_num;
lean_object* v_projDecls_1418_ = stack[3].m_obj;
lean_object* v___y_1419_ = stack[4].m_obj;
lean_object* v___y_1420_ = stack[5].m_obj;
lean_object* v___y_1421_ = stack[6].m_obj;
lean_object* v___y_1422_ = stack[7].m_obj;
lean_object* v_res_1483_;
v_res_1483_ = l_Lean_Meta_mkProjections___lam__2(v_n_1415_, v___x_1416_, v_instImplicit_1417_, v_projDecls_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
stack->m_obj
 = v_res_1483_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1484_, lean_object* v___x_1485_, lean_object* v_instImplicit_1486_, lean_object* v_projDecls_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v_instImplicit_boxed_1493_; lean_object* v_res_1494_; 
v_instImplicit_boxed_1493_ = lean_unbox(v_instImplicit_1486_);
v_res_1494_ = l_Lean_Meta_mkProjections___lam__2(v_n_1484_, v___x_1485_, v_instImplicit_boxed_1493_, v_projDecls_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___x_1485_);
return v_res_1494_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_unsigned_to_nat(32u);
v___x_1498_ = lean_mk_empty_array_with_capacity(v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = ((size_t)5ULL);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_unsigned_to_nat(32u);
v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
lean_ctor_set(v___x_1505_, 2, v___x_1501_);
lean_ctor_set(v___x_1505_, 3, v___x_1501_);
lean_ctor_set_usize(v___x_1505_, 4, v___x_1500_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_box(1);
v___x_1507_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1507_);
lean_ctor_set(v___x_1509_, 2, v___x_1506_);
return v___x_1509_;
}
}
lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1512_, lean_object* v_projDecls_1513_, uint8_t v_instImplicit_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_box(v_instImplicit_1514_);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1522_, 0, v_n_1512_);
lean_closure_set(v___f_1522_, 1, v___x_1520_);
lean_closure_set(v___f_1522_, 2, v___x_1521_);
lean_closure_set(v___f_1522_, 3, v_projDecls_1513_);
v___x_1523_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1524_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1525_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1523_, v___x_1524_, v___f_1522_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1525_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkProjections_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1512_ = stack[0].m_obj;
lean_object* v_projDecls_1513_ = stack[1].m_obj;
uint8_t v_instImplicit_1514_ = stack[2].m_num;
lean_object* v_a_1515_ = stack[3].m_obj;
lean_object* v_a_1516_ = stack[4].m_obj;
lean_object* v_a_1517_ = stack[5].m_obj;
lean_object* v_a_1518_ = stack[6].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l_Lean_Meta_mkProjections(v_n_1512_, v_projDecls_1513_, v_instImplicit_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1527_, lean_object* v_projDecls_1528_, lean_object* v_instImplicit_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
uint8_t v_instImplicit_boxed_1535_; lean_object* v_res_1536_; 
v_instImplicit_boxed_1535_ = lean_unbox(v_instImplicit_1529_);
v_res_1536_ = l_Lean_Meta_mkProjections(v_n_1527_, v_projDecls_1528_, v_instImplicit_boxed_1535_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1536_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1537_, lean_object* v_as_1538_, size_t v_sz_1539_, size_t v_i_1540_, lean_object* v_b_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1537_, v_as_1538_, v_sz_1539_, v_i_1540_, v_b_1541_, v___y_1542_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_instImplicit_1537_ = stack[0].m_num;
lean_object* v_as_1538_ = stack[1].m_obj;
size_t v_sz_1539_ = stack[2].m_num;
size_t v_i_1540_ = stack[3].m_num;
lean_object* v_b_1541_ = stack[4].m_obj;
lean_object* v___y_1542_ = stack[5].m_obj;
lean_object* v___y_1543_ = stack[6].m_obj;
lean_object* v___y_1544_ = stack[7].m_obj;
lean_object* v___y_1545_ = stack[8].m_obj;
lean_object* v_res_1548_;
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_1537_, v_as_1538_, v_sz_1539_, v_i_1540_, v_b_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
stack->m_obj
 = v_res_1548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1549_, lean_object* v_as_1550_, lean_object* v_sz_1551_, lean_object* v_i_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
uint8_t v_instImplicit_boxed_1559_; size_t v_sz_boxed_1560_; size_t v_i_boxed_1561_; lean_object* v_res_1562_; 
v_instImplicit_boxed_1559_ = lean_unbox(v_instImplicit_1549_);
v_sz_boxed_1560_ = lean_unbox_usize(v_sz_1551_);
lean_dec(v_sz_1551_);
v_i_boxed_1561_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_res_1562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1559_, v_as_1550_, v_sz_boxed_1560_, v_i_boxed_1561_, v_b_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec_ref(v_as_1550_);
return v_res_1562_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1563_, uint8_t v_s_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1563_, v_s_1564_, v___y_1566_, v___y_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1563_ = stack[0].m_obj;
uint8_t v_s_1564_ = stack[1].m_num;
lean_object* v___y_1565_ = stack[2].m_obj;
lean_object* v___y_1566_ = stack[3].m_obj;
lean_object* v___y_1567_ = stack[4].m_obj;
lean_object* v___y_1568_ = stack[5].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1563_, v_s_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1572_, lean_object* v_s_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_s_boxed_1579_; lean_object* v_res_1580_; 
v_s_boxed_1579_ = lean_unbox(v_s_1573_);
v_res_1580_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1572_, v_s_boxed_1579_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1580_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1581_, lean_object* v_ref_1582_, lean_object* v_msg_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1582_, v_msg_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1582_ = stack[1].m_obj;
lean_object* v_msg_1583_ = stack[2].m_obj;
lean_object* v___y_1584_ = stack[3].m_obj;
lean_object* v___y_1585_ = stack[4].m_obj;
lean_object* v___y_1586_ = stack[5].m_obj;
lean_object* v___y_1587_ = stack[6].m_obj;
lean_object* v_res_1590_;
v_res_1590_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_box(0), v_ref_1582_, v_msg_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
stack->m_obj
 = v_res_1590_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_ref_1592_, lean_object* v_msg_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1591_, v_ref_1592_, v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v_ref_1592_);
return v_res_1599_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1600_, lean_object* v_x_1601_, uint8_t v_isExporting_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1601_, v_isExporting_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
return v___x_1608_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1601_ = stack[1].m_obj;
uint8_t v_isExporting_1602_ = stack[2].m_num;
lean_object* v___y_1603_ = stack[3].m_obj;
lean_object* v___y_1604_ = stack[4].m_obj;
lean_object* v___y_1605_ = stack[5].m_obj;
lean_object* v___y_1606_ = stack[6].m_obj;
lean_object* v_res_1609_;
v_res_1609_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_box(0), v_x_1601_, v_isExporting_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
stack->m_obj
 = v_res_1609_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1610_, lean_object* v_x_1611_, lean_object* v_isExporting_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v_isExporting_boxed_1618_; lean_object* v_res_1619_; 
v_isExporting_boxed_1618_ = lean_unbox(v_isExporting_1612_);
v_res_1619_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1610_, v_x_1611_, v_isExporting_boxed_1618_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1619_;
}
}
lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1620_, lean_object* v_x_1621_, uint8_t v_when_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1621_, v_when_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1621_ = stack[1].m_obj;
uint8_t v_when_1622_ = stack[2].m_num;
lean_object* v___y_1623_ = stack[3].m_obj;
lean_object* v___y_1624_ = stack[4].m_obj;
lean_object* v___y_1625_ = stack[5].m_obj;
lean_object* v___y_1626_ = stack[6].m_obj;
lean_object* v_res_1629_;
v_res_1629_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_box(0), v_x_1621_, v_when_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_x_1631_, lean_object* v_when_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
uint8_t v_when_boxed_1638_; lean_object* v_res_1639_; 
v_when_boxed_1638_ = lean_unbox(v_when_1632_);
v_res_1639_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1630_, v_x_1631_, v_when_boxed_1638_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
return v_res_1639_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1640_, lean_object* v_projDecls_1641_, lean_object* v___x_1642_, lean_object* v___x_1643_, uint8_t v_instImplicit_1644_, lean_object* v___x_1645_, lean_object* v_params_1646_, lean_object* v_self_1647_, lean_object* v_a_1648_, lean_object* v___x_1649_, lean_object* v_n_1650_, lean_object* v___x_1651_, uint8_t v_a_1652_, lean_object* v_inst_1653_, lean_object* v_R_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_, lean_object* v_c_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1640_, v_projDecls_1641_, v___x_1642_, v___x_1643_, v_instImplicit_1644_, v___x_1645_, v_params_1646_, v_self_1647_, v_a_1648_, v___x_1649_, v_n_1650_, v___x_1651_, v_a_1652_, v_a_1655_, v_b_1656_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1640_ = stack[0].m_obj;
lean_object* v_projDecls_1641_ = stack[1].m_obj;
lean_object* v___x_1642_ = stack[2].m_obj;
lean_object* v___x_1643_ = stack[3].m_obj;
uint8_t v_instImplicit_1644_ = stack[4].m_num;
lean_object* v___x_1645_ = stack[5].m_obj;
lean_object* v_params_1646_ = stack[6].m_obj;
lean_object* v_self_1647_ = stack[7].m_obj;
lean_object* v_a_1648_ = stack[8].m_obj;
lean_object* v___x_1649_ = stack[9].m_obj;
lean_object* v_n_1650_ = stack[10].m_obj;
lean_object* v___x_1651_ = stack[11].m_obj;
uint8_t v_a_1652_ = stack[12].m_num;
lean_object* v_a_1655_ = stack[15].m_obj;
lean_object* v_b_1656_ = stack[16].m_obj;
lean_object* v___y_1658_ = stack[18].m_obj;
lean_object* v___y_1659_ = stack[19].m_obj;
lean_object* v___y_1660_ = stack[20].m_obj;
lean_object* v___y_1661_ = stack[21].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1640_, v_projDecls_1641_, v___x_1642_, v___x_1643_, v_instImplicit_1644_, v___x_1645_, v_params_1646_, v_self_1647_, v_a_1648_, v___x_1649_, v_n_1650_, v___x_1651_, v_a_1652_, lean_box(0), lean_box(0), v_a_1655_, v_b_1656_, lean_box(0), v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1665_ = _args[0];
lean_object* v_projDecls_1666_ = _args[1];
lean_object* v___x_1667_ = _args[2];
lean_object* v___x_1668_ = _args[3];
lean_object* v_instImplicit_1669_ = _args[4];
lean_object* v___x_1670_ = _args[5];
lean_object* v_params_1671_ = _args[6];
lean_object* v_self_1672_ = _args[7];
lean_object* v_a_1673_ = _args[8];
lean_object* v___x_1674_ = _args[9];
lean_object* v_n_1675_ = _args[10];
lean_object* v___x_1676_ = _args[11];
lean_object* v_a_1677_ = _args[12];
lean_object* v_inst_1678_ = _args[13];
lean_object* v_R_1679_ = _args[14];
lean_object* v_a_1680_ = _args[15];
lean_object* v_b_1681_ = _args[16];
lean_object* v_c_1682_ = _args[17];
lean_object* v___y_1683_ = _args[18];
lean_object* v___y_1684_ = _args[19];
lean_object* v___y_1685_ = _args[20];
lean_object* v___y_1686_ = _args[21];
lean_object* v___y_1687_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1688_; uint8_t v_a_19980__boxed_1689_; lean_object* v_res_1690_; 
v_instImplicit_boxed_1688_ = lean_unbox(v_instImplicit_1669_);
v_a_19980__boxed_1689_ = lean_unbox(v_a_1677_);
v_res_1690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1665_, v_projDecls_1666_, v___x_1667_, v___x_1668_, v_instImplicit_boxed_1688_, v___x_1670_, v_params_1671_, v_self_1672_, v_a_1673_, v___x_1674_, v_n_1675_, v___x_1676_, v_a_19980__boxed_1689_, v_inst_1678_, v_R_1679_, v_a_1680_, v_b_1681_, v_c_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v_projDecls_1666_);
lean_dec(v_upperBound_1665_);
return v_res_1690_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1691_, uint8_t v_allowLevelAssignments_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1692_, v_k_1691_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1698_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1698_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1691_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_1692_ = stack[1].m_num;
lean_object* v___y_1693_ = stack[2].m_obj;
lean_object* v___y_1694_ = stack[3].m_obj;
lean_object* v___y_1695_ = stack[4].m_obj;
lean_object* v___y_1696_ = stack[5].m_obj;
lean_object* v_res_1715_;
v_res_1715_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1691_, v_allowLevelAssignments_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
stack->m_obj
 = v_res_1715_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1716_, lean_object* v_allowLevelAssignments_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1723_; lean_object* v_res_1724_; 
v_allowLevelAssignments_boxed_1723_ = lean_unbox(v_allowLevelAssignments_1717_);
v_res_1724_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1716_, v_allowLevelAssignments_boxed_1723_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1724_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1725_, lean_object* v_k_1726_, uint8_t v_allowLevelAssignments_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1726_, v_allowLevelAssignments_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1726_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_1727_ = stack[2].m_num;
lean_object* v___y_1728_ = stack[3].m_obj;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v___y_1730_ = stack[5].m_obj;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_box(0), v_k_1726_, v_allowLevelAssignments_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_k_1736_, lean_object* v_allowLevelAssignments_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1743_; lean_object* v_res_1744_; 
v_allowLevelAssignments_boxed_1743_ = lean_unbox(v_allowLevelAssignments_1737_);
v_res_1744_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1735_, v_k_1736_, v_allowLevelAssignments_boxed_1743_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1744_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1745_, size_t v_sz_1746_, size_t v_i_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_lt(v_i_1747_, v_sz_1746_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_b_1748_);
return v___x_1755_;
}
else
{
lean_object* v_snd_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1811_; 
v_snd_1756_ = lean_ctor_get(v_b_1748_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_b_1748_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; 
v_unused_1812_ = lean_ctor_get(v_b_1748_, 0);
lean_dec(v_unused_1812_);
v___x_1758_ = v_b_1748_;
v_isShared_1759_ = v_isSharedCheck_1811_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_snd_1756_);
lean_dec(v_b_1748_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1811_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_array_1760_; lean_object* v_start_1761_; lean_object* v_stop_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_array_1760_ = lean_ctor_get(v_snd_1756_, 0);
v_start_1761_ = lean_ctor_get(v_snd_1756_, 1);
v_stop_1762_ = lean_ctor_get(v_snd_1756_, 2);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_nat_dec_lt(v_start_1761_, v_stop_1762_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1766_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1763_);
v___x_1766_ = v___x_1758_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1756_);
v___x_1766_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
else
{
lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1807_; 
lean_inc(v_stop_1762_);
lean_inc(v_start_1761_);
lean_inc_ref(v_array_1760_);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_snd_1756_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; lean_object* v_unused_1809_; lean_object* v_unused_1810_; 
v_unused_1808_ = lean_ctor_get(v_snd_1756_, 2);
lean_dec(v_unused_1808_);
v_unused_1809_ = lean_ctor_get(v_snd_1756_, 1);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v_snd_1756_, 0);
lean_dec(v_unused_1810_);
v___x_1770_ = v_snd_1756_;
v_isShared_1771_ = v_isSharedCheck_1807_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v_snd_1756_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1807_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v_a_1772_ = lean_array_uget_borrowed(v_as_1745_, v_i_1747_);
v___x_1773_ = lean_array_fget(v_array_1760_, v_start_1761_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_start_1761_, v___x_1774_);
lean_dec(v_start_1761_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v___x_1775_);
v___x_1777_ = v___x_1770_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_array_1760_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_stop_1762_);
v___x_1777_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
lean_inc(v_a_1772_);
v___x_1778_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1772_, v___x_1773_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1797_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1797_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1797_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_unbox(v_a_1779_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_a_1779_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v___x_1777_);
lean_ctor_set(v___x_1758_, 0, v___x_1784_);
v___x_1786_ = v___x_1758_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1777_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1786_);
v___x_1788_ = v___x_1781_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_del_object(v___x_1781_);
lean_dec(v_a_1779_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 1, v___x_1777_);
lean_ctor_set(v___x_1758_, 0, v___x_1763_);
v___x_1792_ = v___x_1758_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v___x_1777_);
v___x_1792_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
size_t v___x_1793_; size_t v___x_1794_; 
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1747_, v___x_1793_);
v_i_1747_ = v___x_1794_;
v_b_1748_ = v___x_1792_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___x_1777_);
lean_del_object(v___x_1758_);
v_a_1798_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1778_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1778_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1745_ = stack[0].m_obj;
size_t v_sz_1746_ = stack[1].m_num;
size_t v_i_1747_ = stack[2].m_num;
lean_object* v_b_1748_ = stack[3].m_obj;
lean_object* v___y_1749_ = stack[4].m_obj;
lean_object* v___y_1750_ = stack[5].m_obj;
lean_object* v___y_1751_ = stack[6].m_obj;
lean_object* v___y_1752_ = stack[7].m_obj;
lean_object* v_res_1813_;
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1745_, v_sz_1746_, v_i_1747_, v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
stack->m_obj
 = v_res_1813_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1814_, lean_object* v_sz_1815_, lean_object* v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
size_t v_sz_boxed_1823_; size_t v_i_boxed_1824_; lean_object* v_res_1825_; 
v_sz_boxed_1823_ = lean_unbox_usize(v_sz_1815_);
lean_dec(v_sz_1815_);
v_i_boxed_1824_ = lean_unbox_usize(v_i_1816_);
lean_dec(v_i_1816_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1814_, v_sz_boxed_1823_, v_i_boxed_1824_, v_b_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v_as_1814_);
return v_res_1825_;
}
}
lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1826_, lean_object* v_params2_1827_, lean_object* v___x_1828_, lean_object* v_params1_1829_, uint8_t v___x_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
if (v___x_1826_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v___x_1828_);
lean_dec_ref(v_params2_1827_);
v___x_1836_ = lean_box(v___x_1826_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; size_t v_sz_1842_; size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = l_Array_toSubarray___redArg(v_params2_1827_, v___x_1838_, v___x_1828_);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1839_);
v_sz_1842_ = lean_array_size(v_params1_1829_);
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1829_, v_sz_1842_, v___x_1843_, v___x_1841_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1858_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1858_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1858_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_fst_1849_; 
v_fst_1849_ = lean_ctor_get(v_a_1845_, 0);
lean_inc(v_fst_1849_);
lean_dec(v_a_1845_);
if (lean_obj_tag(v_fst_1849_) == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(v___x_1830_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1856_; 
v_val_1854_ = lean_ctor_get(v_fst_1849_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v_fst_1849_, 1);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v_val_1854_);
v___x_1856_ = v___x_1847_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_val_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1844_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1844_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1826_ = stack[0].m_num;
lean_object* v_params2_1827_ = stack[1].m_obj;
lean_object* v___x_1828_ = stack[2].m_obj;
lean_object* v_params1_1829_ = stack[3].m_obj;
uint8_t v___x_1830_ = stack[4].m_num;
lean_object* v___y_1831_ = stack[5].m_obj;
lean_object* v___y_1832_ = stack[6].m_obj;
lean_object* v___y_1833_ = stack[7].m_obj;
lean_object* v___y_1834_ = stack[8].m_obj;
lean_object* v_res_1867_;
v_res_1867_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_1826_, v_params2_1827_, v___x_1828_, v_params1_1829_, v___x_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
stack->m_obj
 = v_res_1867_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1868_, lean_object* v_params2_1869_, lean_object* v___x_1870_, lean_object* v_params1_1871_, lean_object* v___x_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_2109__boxed_1878_; uint8_t v___x_2111__boxed_1879_; lean_object* v_res_1880_; 
v___x_2109__boxed_1878_ = lean_unbox(v___x_1868_);
v___x_2111__boxed_1879_ = lean_unbox(v___x_1872_);
v_res_1880_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2109__boxed_1878_, v_params2_1869_, v___x_1870_, v_params1_1871_, v___x_2111__boxed_1879_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec_ref(v_params1_1871_);
return v_res_1880_;
}
}
lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1881_, lean_object* v_params2_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___y_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1888_ = lean_array_get_size(v_params1_1881_);
v___x_1889_ = lean_array_get_size(v_params2_1882_);
v___x_1890_ = lean_nat_dec_eq(v___x_1888_, v___x_1889_);
v___x_1891_ = 1;
v___x_1892_ = lean_box(v___x_1890_);
v___x_1893_ = lean_box(v___x_1891_);
v___y_1894_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1894_, 0, v___x_1892_);
lean_closure_set(v___y_1894_, 1, v_params2_1882_);
lean_closure_set(v___y_1894_, 2, v___x_1889_);
lean_closure_set(v___y_1894_, 3, v_params1_1881_);
lean_closure_set(v___y_1894_, 4, v___x_1893_);
v___x_1895_ = 0;
v___x_1896_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1894_, v___x_1895_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1896_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params1_1881_ = stack[0].m_obj;
lean_object* v_params2_1882_ = stack[1].m_obj;
lean_object* v_a_1883_ = stack[2].m_obj;
lean_object* v_a_1884_ = stack[3].m_obj;
lean_object* v_a_1885_ = stack[4].m_obj;
lean_object* v_a_1886_ = stack[5].m_obj;
lean_object* v_res_1897_;
v_res_1897_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1881_, v_params2_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
stack->m_obj
 = v_res_1897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1898_, lean_object* v_params2_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1898_, v_params2_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_env_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_st_ref_get(v___y_1907_);
v_env_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc_ref(v_env_1910_);
lean_dec(v___x_1909_);
v___x_1911_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1910_, v_declName_1906_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1906_ = stack[0].m_obj;
lean_object* v___y_1907_ = stack[1].m_obj;
lean_object* v_res_1913_;
v_res_1913_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1906_, v___y_1907_);
stack->m_obj
 = v_res_1913_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1914_, v___y_1915_);
lean_dec(v___y_1915_);
return v_res_1917_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1918_, v___y_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1918_ = stack[0].m_obj;
lean_object* v___y_1919_ = stack[1].m_obj;
lean_object* v___y_1920_ = stack[2].m_obj;
lean_object* v___y_1921_ = stack[3].m_obj;
lean_object* v___y_1922_ = stack[4].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
stack->m_obj
 = v_res_1925_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1933_; lean_object* v_dummy_1934_; 
v___x_1933_ = lean_box(0);
v_dummy_1934_ = l_Lean_Expr_sort___override(v___x_1933_);
return v_dummy_1934_;
}
}
lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1935_, lean_object* v_induct_1936_, lean_object* v_params_1937_, lean_object* v_idx_1938_, lean_object* v_e_1939_, lean_object* v_x_x3f_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
if (lean_obj_tag(v_e_1939_) == 11)
{
lean_object* v_typeName_1952_; lean_object* v_idx_1953_; lean_object* v_struct_1954_; uint8_t v___x_2001_; 
v_typeName_1952_ = lean_ctor_get(v_e_1939_, 0);
v_idx_1953_ = lean_ctor_get(v_e_1939_, 1);
v_struct_1954_ = lean_ctor_get(v_e_1939_, 2);
lean_inc_ref(v_struct_1954_);
v___x_2001_ = lean_nat_dec_eq(v_idx_1953_, v_idx_1938_);
if (v___x_2001_ == 0)
{
lean_dec_ref(v_struct_1954_);
lean_dec_ref_known(v_e_1939_, 3);
lean_dec_ref(v_params_1937_);
goto v___jp_1946_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_name_eq(v_induct_1936_, v_typeName_1952_);
if (v___x_2002_ == 0)
{
lean_dec_ref(v_struct_1954_);
lean_dec_ref_known(v_e_1939_, 3);
lean_dec_ref(v_params_1937_);
goto v___jp_1946_;
}
else
{
if (lean_obj_tag(v_x_x3f_1940_) == 0)
{
goto v___jp_1955_;
}
else
{
lean_object* v_val_2003_; uint8_t v___x_2004_; 
v_val_2003_ = lean_ctor_get(v_x_x3f_1940_, 0);
v___x_2004_ = lean_expr_eqv(v_val_2003_, v_struct_1954_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_struct_1954_);
lean_dec_ref_known(v_e_1939_, 3);
lean_dec_ref(v_params_1937_);
goto v___jp_1946_;
}
else
{
goto v___jp_1955_;
}
}
}
}
v___jp_1955_:
{
lean_object* v___x_1956_; 
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_1956_ = lean_infer_type(v_e_1939_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
v___x_1958_ = lean_whnf(v_a_1957_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_dummy_1960_; lean_object* v_nargs_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v_dummy_1960_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1961_ = l_Lean_Expr_getAppNumArgs(v_a_1959_);
lean_inc(v_nargs_1961_);
v___x_1962_ = lean_mk_array(v_nargs_1961_, v_dummy_1960_);
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_sub(v_nargs_1961_, v___x_1963_);
lean_dec(v_nargs_1961_);
v___x_1965_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1959_, v___x_1962_, v___x_1964_);
v___x_1966_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1937_, v___x_1965_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1976_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_unbox(v_a_1967_);
lean_dec(v_a_1967_);
if (v___x_1971_ == 0)
{
lean_del_object(v___x_1969_);
lean_dec_ref(v_struct_1954_);
goto v___jp_1946_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_struct_1954_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
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
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v_struct_1954_);
v_a_1977_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1966_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1966_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_struct_1954_);
lean_dec_ref(v_params_1937_);
v_a_1985_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1958_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1958_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v_struct_1954_);
lean_dec_ref(v_params_1937_);
v_a_1993_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1956_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1956_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Expr_getAppFn(v_e_1939_);
if (lean_obj_tag(v___x_2005_) == 4)
{
lean_object* v_declName_2006_; lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2057_; 
v_declName_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_declName_2006_);
lean_dec_ref_known(v___x_2005_, 2);
v___x_2007_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_2006_, v_a_1944_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2057_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2057_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___y_2013_; lean_object* v___y_2014_; 
if (lean_obj_tag(v_a_2008_) == 1)
{
lean_object* v_val_2042_; lean_object* v_ctorName_2043_; lean_object* v_numParams_2044_; lean_object* v_i_2045_; uint8_t v___y_2047_; uint8_t v___x_2055_; 
v_val_2042_ = lean_ctor_get(v_a_2008_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v_a_2008_, 1);
v_ctorName_2043_ = lean_ctor_get(v_val_2042_, 0);
lean_inc(v_ctorName_2043_);
v_numParams_2044_ = lean_ctor_get(v_val_2042_, 1);
lean_inc(v_numParams_2044_);
v_i_2045_ = lean_ctor_get(v_val_2042_, 2);
lean_inc(v_i_2045_);
lean_dec(v_val_2042_);
v___x_2055_ = lean_name_eq(v_ctorName_2043_, v_ctor_1935_);
lean_dec(v_ctorName_2043_);
if (v___x_2055_ == 0)
{
lean_dec(v_i_2045_);
v___y_2047_ = v___x_2055_;
goto v___jp_2046_;
}
else
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_nat_dec_eq(v_i_2045_, v_idx_1938_);
lean_dec(v_i_2045_);
v___y_2047_ = v___x_2056_;
goto v___jp_2046_;
}
v___jp_2046_:
{
if (v___y_2047_ == 0)
{
lean_dec(v_numParams_2044_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_e_1939_);
lean_dec_ref(v_params_1937_);
goto v___jp_1949_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2048_ = l_Lean_Expr_getAppNumArgs(v_e_1939_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_add(v_numParams_2044_, v___x_2049_);
lean_dec(v_numParams_2044_);
v___x_2051_ = lean_nat_dec_eq(v___x_2048_, v___x_2050_);
lean_dec(v___x_2050_);
lean_dec(v___x_2048_);
if (v___x_2051_ == 0)
{
lean_del_object(v___x_2010_);
lean_dec_ref(v_e_1939_);
lean_dec_ref(v_params_1937_);
goto v___jp_1949_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Expr_appArg_x21(v_e_1939_);
if (lean_obj_tag(v_x_x3f_1940_) == 0)
{
v___y_2013_ = v___x_2052_;
v___y_2014_ = v___x_2049_;
goto v___jp_2012_;
}
else
{
lean_object* v_val_2053_; uint8_t v___x_2054_; 
v_val_2053_ = lean_ctor_get(v_x_x3f_1940_, 0);
v___x_2054_ = lean_expr_eqv(v_val_2053_, v___x_2052_);
if (v___x_2054_ == 0)
{
lean_dec_ref(v___x_2052_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_e_1939_);
lean_dec_ref(v_params_1937_);
goto v___jp_1949_;
}
else
{
v___y_2013_ = v___x_2052_;
v___y_2014_ = v___x_2049_;
goto v___jp_2012_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_a_2008_);
lean_dec_ref(v_e_1939_);
lean_dec_ref(v_params_1937_);
goto v___jp_1949_;
}
v___jp_2012_:
{
lean_object* v___x_2015_; lean_object* v_dummy_2016_; lean_object* v_nargs_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2015_ = l_Lean_Expr_appFn_x21(v_e_1939_);
lean_dec_ref(v_e_1939_);
v_dummy_2016_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2017_ = l_Lean_Expr_getAppNumArgs(v___x_2015_);
lean_inc(v_nargs_2017_);
v___x_2018_ = lean_mk_array(v_nargs_2017_, v_dummy_2016_);
v___x_2019_ = lean_nat_sub(v_nargs_2017_, v___y_2014_);
lean_dec(v_nargs_2017_);
v___x_2020_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2015_, v___x_2018_, v___x_2019_);
v___x_2021_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1937_, v___x_2020_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2033_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2033_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2026_ == 0)
{
lean_del_object(v___x_2024_);
lean_dec_ref(v___y_2013_);
lean_del_object(v___x_2010_);
goto v___jp_1949_;
}
else
{
lean_object* v___x_2028_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 1);
lean_ctor_set(v___x_2010_, 0, v___y_2013_);
v___x_2028_ = v___x_2010_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___y_2013_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2028_);
v___x_2030_ = v___x_2024_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v___y_2013_);
lean_del_object(v___x_2010_);
v_a_2034_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2021_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2021_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2005_);
lean_dec_ref(v_e_1939_);
lean_dec_ref(v_params_1937_);
goto v___jp_1949_;
}
}
v___jp_1946_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
v___jp_1949_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_1935_ = stack[0].m_obj;
lean_object* v_induct_1936_ = stack[1].m_obj;
lean_object* v_params_1937_ = stack[2].m_obj;
lean_object* v_idx_1938_ = stack[3].m_obj;
lean_object* v_e_1939_ = stack[4].m_obj;
lean_object* v_x_x3f_1940_ = stack[5].m_obj;
lean_object* v_a_1941_ = stack[6].m_obj;
lean_object* v_a_1942_ = stack[7].m_obj;
lean_object* v_a_1943_ = stack[8].m_obj;
lean_object* v_a_1944_ = stack[9].m_obj;
lean_object* v_res_2058_;
v_res_2058_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_1935_, v_induct_1936_, v_params_1937_, v_idx_1938_, v_e_1939_, v_x_x3f_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
stack->m_obj
 = v_res_2058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2059_, lean_object* v_induct_2060_, lean_object* v_params_2061_, lean_object* v_idx_2062_, lean_object* v_e_2063_, lean_object* v_x_x3f_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2059_, v_induct_2060_, v_params_2061_, v_idx_2062_, v_e_2063_, v_x_x3f_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_x_x3f_2064_);
lean_dec(v_idx_2062_);
lean_dec(v_induct_2060_);
lean_dec(v_ctor_2059_);
return v_res_2070_;
}
}
lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_env_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2077_ = lean_st_ref_get(v___y_2075_);
v_env_2081_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_ref(v_env_2081_);
lean_dec(v___x_2077_);
v___x_2082_ = 0;
v___x_2083_ = l_Lean_Environment_findAsync_x3f(v_env_2081_, v_constName_2071_, v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2103_; 
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2103_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_val_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2103_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
uint8_t v_kind_2088_; 
v_kind_2088_ = lean_ctor_get_uint8(v_val_2084_, sizeof(void*)*3);
if (v_kind_2088_ == 6)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2084_);
if (lean_obj_tag(v___x_2089_) == 6)
{
lean_object* v_val_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2100_; 
v_val_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_val_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2100_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_val_2090_);
v___x_2095_ = v___x_2086_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_val_2090_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2095_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2089_);
lean_del_object(v___x_2086_);
v___x_2101_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2102_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2101_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2102_;
}
}
else
{
lean_del_object(v___x_2086_);
lean_dec(v_val_2084_);
goto v___jp_2078_;
}
}
}
else
{
lean_dec(v___x_2083_);
goto v___jp_2078_;
}
v___jp_2078_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
LEAN_EXPORT void l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2071_ = stack[0].m_obj;
lean_object* v___y_2072_ = stack[1].m_obj;
lean_object* v___y_2073_ = stack[2].m_obj;
lean_object* v___y_2074_ = stack[3].m_obj;
lean_object* v___y_2075_ = stack[4].m_obj;
lean_object* v_res_2104_;
v_res_2104_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
stack->m_obj
 = v_res_2104_;
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2111_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v_declName_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_a_2126_, lean_object* v_val_2127_, lean_object* v_a_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_lt(v_a_2128_, v_upperBound_2120_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_a_2128_);
lean_dec_ref(v___x_2125_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_b_2129_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v_b_2129_);
v___x_2137_ = l_Lean_instInhabitedExpr;
v___x_2138_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2139_ = lean_nat_add(v___x_2121_, v_a_2128_);
v___x_2140_ = lean_array_get_borrowed(v___x_2137_, v___x_2122_, v___x_2139_);
lean_dec(v___x_2139_);
lean_inc(v___x_2140_);
lean_inc_ref(v___x_2125_);
v___x_2141_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2123_, v___x_2124_, v___x_2125_, v_a_2128_, v___x_2140_, v_a_2126_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2159_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2159_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2159_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
if (lean_obj_tag(v_a_2142_) == 1)
{
lean_object* v_val_2146_; uint8_t v___x_2147_; 
v_val_2146_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v_a_2142_, 1);
v___x_2147_ = lean_expr_eqv(v_val_2146_, v_val_2127_);
lean_dec(v_val_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_a_2128_);
lean_dec_ref(v___x_2125_);
v___x_2148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2148_);
v___x_2150_ = v___x_2144_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_del_object(v___x_2144_);
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_add(v_a_2128_, v___x_2152_);
lean_dec(v_a_2128_);
v_a_2128_ = v___x_2153_;
v_b_2129_ = v___x_2138_;
goto _start;
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2128_);
lean_dec_ref(v___x_2125_);
v___x_2155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2155_);
v___x_2157_ = v___x_2144_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2128_);
lean_dec_ref(v___x_2125_);
v_a_2160_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2141_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2141_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2120_ = stack[0].m_obj;
lean_object* v___x_2121_ = stack[1].m_obj;
lean_object* v___x_2122_ = stack[2].m_obj;
lean_object* v_declName_2123_ = stack[3].m_obj;
lean_object* v___x_2124_ = stack[4].m_obj;
lean_object* v___x_2125_ = stack[5].m_obj;
lean_object* v_a_2126_ = stack[6].m_obj;
lean_object* v_val_2127_ = stack[7].m_obj;
lean_object* v_a_2128_ = stack[8].m_obj;
lean_object* v_b_2129_ = stack[9].m_obj;
lean_object* v___y_2130_ = stack[10].m_obj;
lean_object* v___y_2131_ = stack[11].m_obj;
lean_object* v___y_2132_ = stack[12].m_obj;
lean_object* v___y_2133_ = stack[13].m_obj;
lean_object* v_res_2168_;
v_res_2168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2120_, v___x_2121_, v___x_2122_, v_declName_2123_, v___x_2124_, v___x_2125_, v_a_2126_, v_val_2127_, v_a_2128_, v_b_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
stack->m_obj
 = v_res_2168_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2169_, lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_declName_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v_a_2175_, lean_object* v_val_2176_, lean_object* v_a_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2169_, v___x_2170_, v___x_2171_, v_declName_2172_, v___x_2173_, v___x_2174_, v_a_2175_, v_val_2176_, v_a_2177_, v_b_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v_val_2176_);
lean_dec(v_a_2175_);
lean_dec(v___x_2173_);
lean_dec(v_declName_2172_);
lean_dec_ref(v___x_2171_);
lean_dec(v___x_2170_);
lean_dec(v_upperBound_2169_);
return v_res_2184_;
}
}
lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2185_, lean_object* v_p_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Expr_getAppFn(v_e_2185_);
if (lean_obj_tag(v___x_2192_) == 4)
{
lean_object* v_declName_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_declName_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_n(v_declName_2193_, 2);
lean_dec_ref_known(v___x_2192_, 2);
v___x_2194_ = l_Lean_instInhabitedExpr;
v___x_2195_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2193_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2267_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2267_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2267_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_val_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2264_; 
v_val_2205_ = lean_ctor_get(v_a_2196_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2196_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2207_ = v_a_2196_;
v_isShared_2208_ = v_isSharedCheck_2264_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_val_2205_);
lean_dec(v_a_2196_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2264_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_induct_2209_; lean_object* v_numParams_2210_; lean_object* v_numFields_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_induct_2209_ = lean_ctor_get(v_val_2205_, 1);
lean_inc_n(v_induct_2209_, 2);
v_numParams_2210_ = lean_ctor_get(v_val_2205_, 3);
lean_inc(v_numParams_2210_);
v_numFields_2211_ = lean_ctor_get(v_val_2205_, 4);
lean_inc(v_numFields_2211_);
lean_dec(v_val_2205_);
v___x_2212_ = lean_apply_1(v_p_2186_, v_induct_2209_);
v___x_2213_ = lean_unbox(v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_dec(v_numFields_2211_);
lean_dec(v_numParams_2210_);
lean_dec(v_induct_2209_);
lean_del_object(v___x_2198_);
lean_dec(v_declName_2193_);
lean_dec_ref(v_e_2185_);
v___x_2214_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set_tag(v___x_2207_, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2214_);
v___x_2216_ = v___x_2207_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
else
{
lean_object* v___x_2218_; uint8_t v___x_2219_; 
lean_del_object(v___x_2207_);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_nat_dec_lt(v___x_2218_, v_numFields_2211_);
if (v___x_2219_ == 0)
{
lean_dec(v_numFields_2211_);
lean_dec(v_numParams_2210_);
lean_dec(v_induct_2209_);
lean_dec(v_declName_2193_);
lean_dec_ref(v_e_2185_);
goto v___jp_2200_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = l_Lean_Expr_getAppNumArgs(v_e_2185_);
v___x_2221_ = lean_nat_add(v_numParams_2210_, v_numFields_2211_);
v___x_2222_ = lean_nat_dec_eq(v___x_2220_, v___x_2221_);
lean_dec(v___x_2221_);
if (v___x_2222_ == 0)
{
lean_dec(v___x_2220_);
lean_dec(v_numFields_2211_);
lean_dec(v_numParams_2210_);
lean_dec(v_induct_2209_);
lean_dec(v_declName_2193_);
lean_dec_ref(v_e_2185_);
goto v___jp_2200_;
}
else
{
lean_object* v_dummy_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_del_object(v___x_2198_);
v_dummy_2223_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2220_);
v___x_2224_ = lean_mk_array(v___x_2220_, v_dummy_2223_);
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_nat_sub(v___x_2220_, v___x_2225_);
lean_dec(v___x_2220_);
v___x_2227_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2185_, v___x_2224_, v___x_2226_);
lean_inc(v_numParams_2210_);
v___x_2228_ = l_Array_extract___redArg(v___x_2227_, v___x_2218_, v_numParams_2210_);
v___x_2229_ = lean_array_get_borrowed(v___x_2194_, v___x_2227_, v_numParams_2210_);
v___x_2230_ = lean_box(0);
lean_inc(v___x_2229_);
lean_inc_ref(v___x_2228_);
v___x_2231_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2193_, v_induct_2209_, v___x_2228_, v___x_2218_, v___x_2229_, v___x_2230_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2263_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2263_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2263_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
if (lean_obj_tag(v_a_2232_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_del_object(v___x_2234_);
v_val_2236_ = lean_ctor_get(v_a_2232_, 0);
v___x_2237_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2211_, v_numParams_2210_, v___x_2227_, v_declName_2193_, v_induct_2209_, v___x_2228_, v_a_2232_, v_val_2236_, v___x_2225_, v___x_2237_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_induct_2209_);
lean_dec(v_declName_2193_);
lean_dec_ref(v___x_2227_);
lean_dec(v_numParams_2210_);
lean_dec(v_numFields_2211_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2251_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2251_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_fst_2243_; 
v_fst_2243_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_fst_2243_);
lean_dec(v_a_2239_);
if (lean_obj_tag(v_fst_2243_) == 0)
{
lean_object* v___x_2245_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_a_2232_);
v___x_2245_ = v___x_2241_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2232_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
else
{
lean_object* v_val_2247_; lean_object* v___x_2249_; 
lean_dec_ref_known(v_a_2232_, 1);
v_val_2247_ = lean_ctor_get(v_fst_2243_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v_fst_2243_, 1);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_val_2247_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_val_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref_known(v_a_2232_, 1);
v_a_2252_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2238_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2238_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v___x_2261_; 
lean_dec(v_a_2232_);
lean_dec_ref(v___x_2228_);
lean_dec_ref(v___x_2227_);
lean_dec(v_numFields_2211_);
lean_dec(v_numParams_2210_);
lean_dec(v_induct_2209_);
lean_dec(v_declName_2193_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2230_);
v___x_2261_ = v___x_2234_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2230_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_dec_ref(v___x_2228_);
lean_dec_ref(v___x_2227_);
lean_dec(v_numFields_2211_);
lean_dec(v_numParams_2210_);
lean_dec(v_induct_2209_);
lean_dec(v_declName_2193_);
return v___x_2231_;
}
}
}
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_del_object(v___x_2198_);
lean_dec(v_a_2196_);
lean_dec(v_declName_2193_);
lean_dec_ref(v_p_2186_);
lean_dec_ref(v_e_2185_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
v___jp_2200_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_box(0);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
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
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_declName_2193_);
lean_dec_ref(v_p_2186_);
lean_dec_ref(v_e_2185_);
v_a_2268_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2195_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2195_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v___x_2192_);
lean_dec_ref(v_p_2186_);
lean_dec_ref(v_e_2185_);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_etaStruct_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2185_ = stack[0].m_obj;
lean_object* v_p_2186_ = stack[1].m_obj;
lean_object* v_a_2187_ = stack[2].m_obj;
lean_object* v_a_2188_ = stack[3].m_obj;
lean_object* v_a_2189_ = stack[4].m_obj;
lean_object* v_a_2190_ = stack[5].m_obj;
lean_object* v_res_2278_;
v_res_2278_ = l_Lean_Meta_etaStruct_x3f(v_e_2185_, v_p_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
stack->m_obj
 = v_res_2278_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2279_, lean_object* v_p_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Meta_etaStruct_x3f(v_e_2279_, v_p_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2286_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2287_, lean_object* v___x_2288_, lean_object* v___x_2289_, lean_object* v_declName_2290_, lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v_a_2293_, lean_object* v_val_2294_, lean_object* v_inst_2295_, lean_object* v_R_2296_, lean_object* v_a_2297_, lean_object* v_b_2298_, lean_object* v_c_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2287_, v___x_2288_, v___x_2289_, v_declName_2290_, v___x_2291_, v___x_2292_, v_a_2293_, v_val_2294_, v_a_2297_, v_b_2298_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v___x_2305_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2287_ = stack[0].m_obj;
lean_object* v___x_2288_ = stack[1].m_obj;
lean_object* v___x_2289_ = stack[2].m_obj;
lean_object* v_declName_2290_ = stack[3].m_obj;
lean_object* v___x_2291_ = stack[4].m_obj;
lean_object* v___x_2292_ = stack[5].m_obj;
lean_object* v_a_2293_ = stack[6].m_obj;
lean_object* v_val_2294_ = stack[7].m_obj;
lean_object* v_a_2297_ = stack[10].m_obj;
lean_object* v_b_2298_ = stack[11].m_obj;
lean_object* v___y_2300_ = stack[13].m_obj;
lean_object* v___y_2301_ = stack[14].m_obj;
lean_object* v___y_2302_ = stack[15].m_obj;
lean_object* v___y_2303_ = stack[16].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2287_, v___x_2288_, v___x_2289_, v_declName_2290_, v___x_2291_, v___x_2292_, v_a_2293_, v_val_2294_, lean_box(0), lean_box(0), v_a_2297_, v_b_2298_, lean_box(0), v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2307_ = _args[0];
lean_object* v___x_2308_ = _args[1];
lean_object* v___x_2309_ = _args[2];
lean_object* v_declName_2310_ = _args[3];
lean_object* v___x_2311_ = _args[4];
lean_object* v___x_2312_ = _args[5];
lean_object* v_a_2313_ = _args[6];
lean_object* v_val_2314_ = _args[7];
lean_object* v_inst_2315_ = _args[8];
lean_object* v_R_2316_ = _args[9];
lean_object* v_a_2317_ = _args[10];
lean_object* v_b_2318_ = _args[11];
lean_object* v_c_2319_ = _args[12];
lean_object* v___y_2320_ = _args[13];
lean_object* v___y_2321_ = _args[14];
lean_object* v___y_2322_ = _args[15];
lean_object* v___y_2323_ = _args[16];
lean_object* v___y_2324_ = _args[17];
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2307_, v___x_2308_, v___x_2309_, v_declName_2310_, v___x_2311_, v___x_2312_, v_a_2313_, v_val_2314_, v_inst_2315_, v_R_2316_, v_a_2317_, v_b_2318_, v_c_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_val_2314_);
lean_dec(v_a_2313_);
lean_dec(v___x_2311_);
lean_dec(v_declName_2310_);
lean_dec_ref(v___x_2309_);
lean_dec(v___x_2308_);
lean_dec(v_upperBound_2307_);
return v_res_2325_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v___x_2329_; 
v___x_2329_ = l_Lean_Expr_hasMVar(v_e_2326_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_e_2326_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v_mctx_2332_; lean_object* v___x_2333_; lean_object* v_fst_2334_; lean_object* v_snd_2335_; lean_object* v___x_2336_; lean_object* v_cache_2337_; lean_object* v_zetaDeltaFVarIds_2338_; lean_object* v_postponed_2339_; lean_object* v_diag_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2349_; 
v___x_2331_ = lean_st_ref_get(v___y_2327_);
v_mctx_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_ref(v_mctx_2332_);
lean_dec(v___x_2331_);
v___x_2333_ = l_Lean_instantiateMVarsCore(v_mctx_2332_, v_e_2326_);
v_fst_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_fst_2334_);
v_snd_2335_ = lean_ctor_get(v___x_2333_, 1);
lean_inc(v_snd_2335_);
lean_dec_ref(v___x_2333_);
v___x_2336_ = lean_st_ref_take(v___y_2327_);
v_cache_2337_ = lean_ctor_get(v___x_2336_, 1);
v_zetaDeltaFVarIds_2338_ = lean_ctor_get(v___x_2336_, 2);
v_postponed_2339_ = lean_ctor_get(v___x_2336_, 3);
v_diag_2340_ = lean_ctor_get(v___x_2336_, 4);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v___x_2336_, 0);
lean_dec(v_unused_2350_);
v___x_2342_ = v___x_2336_;
v_isShared_2343_ = v_isSharedCheck_2349_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_diag_2340_);
lean_inc(v_postponed_2339_);
lean_inc(v_zetaDeltaFVarIds_2338_);
lean_inc(v_cache_2337_);
lean_dec(v___x_2336_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2349_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v_snd_2335_);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_snd_2335_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_cache_2337_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_zetaDeltaFVarIds_2338_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_postponed_2339_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_diag_2340_);
v___x_2345_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_st_ref_put(v___y_2327_, v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_fst_2334_);
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2326_ = stack[0].m_obj;
lean_object* v___y_2327_ = stack[1].m_obj;
lean_object* v_res_2351_;
v_res_2351_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2326_, v___y_2327_);
stack->m_obj
 = v_res_2351_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2352_, v___y_2353_);
lean_dec(v___y_2353_);
return v_res_2355_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2356_, v___y_2358_);
return v___x_2362_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2356_ = stack[0].m_obj;
lean_object* v___y_2357_ = stack[1].m_obj;
lean_object* v___y_2358_ = stack[2].m_obj;
lean_object* v___y_2359_ = stack[3].m_obj;
lean_object* v___y_2360_ = stack[4].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
return v_res_2370_;
}
}
lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT void l_Lean_Meta_etaStructReduce___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2373_ = stack[0].m_obj;
lean_object* v___y_2374_ = stack[1].m_obj;
lean_object* v___y_2375_ = stack[2].m_obj;
lean_object* v___y_2376_ = stack[3].m_obj;
lean_object* v___y_2377_ = stack[4].m_obj;
lean_object* v_res_2381_;
v_res_2381_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
stack->m_obj
 = v_res_2381_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_x_2382_);
return v_res_2388_;
}
}
lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2389_, lean_object* v_e_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Meta_etaStruct_x3f(v_e_2390_, v_p_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2416_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2416_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2416_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
if (lean_obj_tag(v_a_2397_) == 1)
{
lean_object* v_val_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2411_; 
v_val_2401_ = lean_ctor_get(v_a_2397_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_a_2397_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2403_ = v_a_2397_;
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_val_2401_);
lean_dec(v_a_2397_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2411_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 0);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_val_2401_);
v___x_2406_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2408_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2406_);
v___x_2408_ = v___x_2399_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_dec(v_a_2397_);
v___x_2412_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2412_);
v___x_2414_ = v___x_2399_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
v_a_2417_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2396_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2396_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_etaStructReduce___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2389_ = stack[0].m_obj;
lean_object* v_e_2390_ = stack[1].m_obj;
lean_object* v___y_2391_ = stack[2].m_obj;
lean_object* v___y_2392_ = stack[3].m_obj;
lean_object* v___y_2393_ = stack[4].m_obj;
lean_object* v___y_2394_ = stack[5].m_obj;
lean_object* v_res_2425_;
v_res_2425_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2389_, v_e_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
stack->m_obj
 = v_res_2425_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2426_, lean_object* v_e_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2426_, v_e_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_apply_1(v_x_2435_, lean_box(0));
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2435_ = stack[1].m_obj;
lean_object* v___y_2436_ = stack[2].m_obj;
lean_object* v___y_2437_ = stack[3].m_obj;
lean_object* v___y_2438_ = stack[4].m_obj;
lean_object* v___y_2439_ = stack[5].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2444_, v_x_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2452_, lean_object* v_b_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2454_) == 0)
{
lean_dec(v_b_2453_);
lean_dec_ref(v_a_2452_);
return v_x_2454_;
}
else
{
lean_object* v_key_2455_; lean_object* v_value_2456_; lean_object* v_tail_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2469_; 
v_key_2455_ = lean_ctor_get(v_x_2454_, 0);
v_value_2456_ = lean_ctor_get(v_x_2454_, 1);
v_tail_2457_ = lean_ctor_get(v_x_2454_, 2);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_x_2454_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2459_ = v_x_2454_;
v_isShared_2460_ = v_isSharedCheck_2469_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_tail_2457_);
lean_inc(v_value_2456_);
lean_inc(v_key_2455_);
lean_dec(v_x_2454_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2469_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
uint8_t v___x_2461_; 
v___x_2461_ = l_Lean_ExprStructEq_beq(v_key_2455_, v_a_2452_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2452_, v_b_2453_, v_tail_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 2, v___x_2462_);
v___x_2464_ = v___x_2459_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_key_2455_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_value_2456_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
else
{
lean_object* v___x_2467_; 
lean_dec(v_value_2456_);
lean_dec(v_key_2455_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v_b_2453_);
lean_ctor_set(v___x_2459_, 0, v_a_2452_);
v___x_2467_ = v___x_2459_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2452_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_b_2453_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_tail_2457_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 0)
{
return v_x_2470_;
}
else
{
lean_object* v_key_2472_; lean_object* v_value_2473_; lean_object* v_tail_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2497_; 
v_key_2472_ = lean_ctor_get(v_x_2471_, 0);
v_value_2473_ = lean_ctor_get(v_x_2471_, 1);
v_tail_2474_ = lean_ctor_get(v_x_2471_, 2);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2471_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2476_ = v_x_2471_;
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_tail_2474_);
lean_inc(v_value_2473_);
lean_inc(v_key_2472_);
lean_dec(v_x_2471_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; uint64_t v___x_2479_; uint64_t v___x_2480_; uint64_t v___x_2481_; uint64_t v_fold_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v___x_2485_; size_t v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; size_t v___x_2489_; size_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2478_ = lean_array_get_size(v_x_2470_);
v___x_2479_ = l_Lean_ExprStructEq_hash(v_key_2472_);
v___x_2480_ = 32ULL;
v___x_2481_ = lean_uint64_shift_right(v___x_2479_, v___x_2480_);
v_fold_2482_ = lean_uint64_xor(v___x_2479_, v___x_2481_);
v___x_2483_ = 16ULL;
v___x_2484_ = lean_uint64_shift_right(v_fold_2482_, v___x_2483_);
v___x_2485_ = lean_uint64_xor(v_fold_2482_, v___x_2484_);
v___x_2486_ = lean_uint64_to_usize(v___x_2485_);
v___x_2487_ = lean_usize_of_nat(v___x_2478_);
v___x_2488_ = ((size_t)1ULL);
v___x_2489_ = lean_usize_sub(v___x_2487_, v___x_2488_);
v___x_2490_ = lean_usize_land(v___x_2486_, v___x_2489_);
v___x_2491_ = lean_array_uget_borrowed(v_x_2470_, v___x_2490_);
lean_inc(v___x_2491_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 2, v___x_2491_);
v___x_2493_ = v___x_2476_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_key_2472_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_value_2473_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_array_uset(v_x_2470_, v___x_2490_, v___x_2493_);
v_x_2470_ = v___x_2494_;
v_x_2471_ = v_tail_2474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2498_, lean_object* v_source_2499_, lean_object* v_target_2500_){
_start:
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = lean_array_get_size(v_source_2499_);
v___x_2502_ = lean_nat_dec_lt(v_i_2498_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v_source_2499_);
lean_dec(v_i_2498_);
return v_target_2500_;
}
else
{
lean_object* v_es_2503_; lean_object* v___x_2504_; lean_object* v_source_2505_; lean_object* v_target_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_es_2503_ = lean_array_fget(v_source_2499_, v_i_2498_);
v___x_2504_ = lean_box(0);
v_source_2505_ = lean_array_fset(v_source_2499_, v_i_2498_, v___x_2504_);
v_target_2506_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2500_, v_es_2503_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_i_2498_, v___x_2507_);
lean_dec(v_i_2498_);
v_i_2498_ = v___x_2508_;
v_source_2499_ = v_source_2505_;
v_target_2500_ = v_target_2506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_nbuckets_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2511_ = lean_array_get_size(v_data_2510_);
v___x_2512_ = lean_unsigned_to_nat(2u);
v_nbuckets_2513_ = lean_nat_mul(v___x_2511_, v___x_2512_);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_mk_array(v_nbuckets_2513_, v___x_2515_);
v___x_2517_ = lean_array_propagate_mark(v_data_2510_, v___x_2516_);
v___x_2518_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2514_, v_data_2510_, v___x_2517_);
return v___x_2518_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2519_, lean_object* v_x_2520_){
_start:
{
if (lean_obj_tag(v_x_2520_) == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = 0;
return v___x_2521_;
}
else
{
lean_object* v_key_2522_; lean_object* v_tail_2523_; uint8_t v___x_2524_; 
v_key_2522_ = lean_ctor_get(v_x_2520_, 0);
v_tail_2523_ = lean_ctor_get(v_x_2520_, 2);
v___x_2524_ = l_Lean_ExprStructEq_beq(v_key_2522_, v_a_2519_);
if (v___x_2524_ == 0)
{
v_x_2520_ = v_tail_2523_;
goto _start;
}
else
{
return v___x_2524_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2519_ = stack[0].m_obj;
lean_object* v_x_2520_ = stack[1].m_obj;
uint8_t v_res_2526_;
v_res_2526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2519_, v_x_2520_);
stack->m_num = v_res_2526_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2527_, lean_object* v_x_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2527_, v_x_2528_);
lean_dec(v_x_2528_);
lean_dec_ref(v_a_2527_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2531_, lean_object* v_a_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v_size_2534_; lean_object* v_buckets_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2578_; 
v_size_2534_ = lean_ctor_get(v_m_2531_, 0);
v_buckets_2535_ = lean_ctor_get(v_m_2531_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_m_2531_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2537_ = v_m_2531_;
v_isShared_2538_ = v_isSharedCheck_2578_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_buckets_2535_);
lean_inc(v_size_2534_);
lean_dec(v_m_2531_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2578_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; uint64_t v___x_2540_; uint64_t v___x_2541_; uint64_t v___x_2542_; uint64_t v_fold_2543_; uint64_t v___x_2544_; uint64_t v___x_2545_; uint64_t v___x_2546_; size_t v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; lean_object* v_bkt_2552_; uint8_t v___x_2553_; 
v___x_2539_ = lean_array_get_size(v_buckets_2535_);
v___x_2540_ = l_Lean_ExprStructEq_hash(v_a_2532_);
v___x_2541_ = 32ULL;
v___x_2542_ = lean_uint64_shift_right(v___x_2540_, v___x_2541_);
v_fold_2543_ = lean_uint64_xor(v___x_2540_, v___x_2542_);
v___x_2544_ = 16ULL;
v___x_2545_ = lean_uint64_shift_right(v_fold_2543_, v___x_2544_);
v___x_2546_ = lean_uint64_xor(v_fold_2543_, v___x_2545_);
v___x_2547_ = lean_uint64_to_usize(v___x_2546_);
v___x_2548_ = lean_usize_of_nat(v___x_2539_);
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_sub(v___x_2548_, v___x_2549_);
v___x_2551_ = lean_usize_land(v___x_2547_, v___x_2550_);
v_bkt_2552_ = lean_array_uget_borrowed(v_buckets_2535_, v___x_2551_);
v___x_2553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2532_, v_bkt_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v_size_x27_2555_; lean_object* v___x_2556_; lean_object* v_buckets_x27_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v_size_x27_2555_ = lean_nat_add(v_size_2534_, v___x_2554_);
lean_dec(v_size_2534_);
lean_inc(v_bkt_2552_);
v___x_2556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2532_);
lean_ctor_set(v___x_2556_, 1, v_b_2533_);
lean_ctor_set(v___x_2556_, 2, v_bkt_2552_);
v_buckets_x27_2557_ = lean_array_uset(v_buckets_2535_, v___x_2551_, v___x_2556_);
v___x_2558_ = lean_unsigned_to_nat(4u);
v___x_2559_ = lean_nat_mul(v_size_x27_2555_, v___x_2558_);
v___x_2560_ = lean_unsigned_to_nat(3u);
v___x_2561_ = lean_nat_div(v___x_2559_, v___x_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_array_get_size(v_buckets_x27_2557_);
v___x_2563_ = lean_nat_dec_le(v___x_2561_, v___x_2562_);
lean_dec(v___x_2561_);
if (v___x_2563_ == 0)
{
lean_object* v_val_2564_; lean_object* v___x_2566_; 
v_val_2564_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2557_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v_val_2564_);
lean_ctor_set(v___x_2537_, 0, v_size_x27_2555_);
v___x_2566_ = v___x_2537_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_size_x27_2555_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_val_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2569_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v_buckets_x27_2557_);
lean_ctor_set(v___x_2537_, 0, v_size_x27_2555_);
v___x_2569_ = v___x_2537_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_size_x27_2555_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_buckets_x27_2557_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v_buckets_x27_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_inc(v_bkt_2552_);
v___x_2571_ = lean_box(0);
v_buckets_x27_2572_ = lean_array_uset(v_buckets_2535_, v___x_2551_, v___x_2571_);
v___x_2573_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2532_, v_b_2533_, v_bkt_2552_);
v___x_2574_ = lean_array_uset(v_buckets_x27_2572_, v___x_2551_, v___x_2573_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v___x_2574_);
v___x_2576_ = v___x_2537_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_size_2534_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2579_, lean_object* v_e_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2583_ = lean_st_ref_take(v_a_2579_);
v___x_2584_ = lean_box(0);
v___x_2585_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2583_, v_e_2580_, v_a_2581_);
v___x_2586_ = lean_st_ref_put(v_a_2579_, v___x_2585_);
return v___x_2584_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2579_ = stack[0].m_obj;
lean_object* v_e_2580_ = stack[1].m_obj;
lean_object* v_a_2581_ = stack[2].m_obj;
lean_object* v_res_2587_;
v_res_2587_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2579_, v_e_2580_, v_a_2581_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2588_, lean_object* v_e_2589_, lean_object* v_a_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2588_, v_e_2589_, v_a_2590_);
lean_dec(v_a_2588_);
return v_res_2592_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2593_, lean_object* v_x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_apply_1(v_x_2594_, lean_box(0));
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2594_ = stack[1].m_obj;
lean_object* v___y_2595_ = stack[2].m_obj;
lean_object* v___y_2596_ = stack[3].m_obj;
lean_object* v___y_2597_ = stack[4].m_obj;
lean_object* v___y_2598_ = stack[5].m_obj;
lean_object* v_res_2602_;
v_res_2602_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v_x_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
stack->m_obj
 = v_res_2602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2603_, lean_object* v_x_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2603_, v_x_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2611_, lean_object* v_x_2612_){
_start:
{
if (lean_obj_tag(v_x_2612_) == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_box(0);
return v___x_2613_;
}
else
{
lean_object* v_key_2614_; lean_object* v_value_2615_; lean_object* v_tail_2616_; uint8_t v___x_2617_; 
v_key_2614_ = lean_ctor_get(v_x_2612_, 0);
v_value_2615_ = lean_ctor_get(v_x_2612_, 1);
v_tail_2616_ = lean_ctor_get(v_x_2612_, 2);
v___x_2617_ = l_Lean_ExprStructEq_beq(v_key_2614_, v_a_2611_);
if (v___x_2617_ == 0)
{
v_x_2612_ = v_tail_2616_;
goto _start;
}
else
{
lean_object* v___x_2619_; 
lean_inc(v_value_2615_);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_value_2615_);
return v___x_2619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2620_, lean_object* v_x_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2620_, v_x_2621_);
lean_dec(v_x_2621_);
lean_dec_ref(v_a_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_buckets_2625_; lean_object* v___x_2626_; uint64_t v___x_2627_; uint64_t v___x_2628_; uint64_t v___x_2629_; uint64_t v_fold_2630_; uint64_t v___x_2631_; uint64_t v___x_2632_; uint64_t v___x_2633_; size_t v___x_2634_; size_t v___x_2635_; size_t v___x_2636_; size_t v___x_2637_; size_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_buckets_2625_ = lean_ctor_get(v_m_2623_, 1);
v___x_2626_ = lean_array_get_size(v_buckets_2625_);
v___x_2627_ = l_Lean_ExprStructEq_hash(v_a_2624_);
v___x_2628_ = 32ULL;
v___x_2629_ = lean_uint64_shift_right(v___x_2627_, v___x_2628_);
v_fold_2630_ = lean_uint64_xor(v___x_2627_, v___x_2629_);
v___x_2631_ = 16ULL;
v___x_2632_ = lean_uint64_shift_right(v_fold_2630_, v___x_2631_);
v___x_2633_ = lean_uint64_xor(v_fold_2630_, v___x_2632_);
v___x_2634_ = lean_uint64_to_usize(v___x_2633_);
v___x_2635_ = lean_usize_of_nat(v___x_2626_);
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_sub(v___x_2635_, v___x_2636_);
v___x_2638_ = lean_usize_land(v___x_2634_, v___x_2637_);
v___x_2639_ = lean_array_uget_borrowed(v_buckets_2625_, v___x_2638_);
v___x_2640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2624_, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2641_, v_a_2642_);
lean_dec_ref(v_a_2642_);
lean_dec_ref(v_m_2641_);
return v_res_2643_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2644_, lean_object* v___y_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2645_);
v___x_2652_ = lean_apply_7(v_k_2644_, v_b_2646_, v___y_2645_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, lean_box(0));
return v___x_2652_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2644_ = stack[0].m_obj;
lean_object* v___y_2645_ = stack[1].m_obj;
lean_object* v_b_2646_ = stack[2].m_obj;
lean_object* v___y_2647_ = stack[3].m_obj;
lean_object* v___y_2648_ = stack[4].m_obj;
lean_object* v___y_2649_ = stack[5].m_obj;
lean_object* v___y_2650_ = stack[6].m_obj;
lean_object* v_res_2653_;
v_res_2653_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2644_, v___y_2645_, v_b_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
stack->m_obj
 = v_res_2653_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2654_, lean_object* v___y_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2654_, v___y_2655_, v_b_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2655_);
return v_res_2662_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2663_, uint8_t v_bi_2664_, lean_object* v_type_2665_, lean_object* v_k_2666_, uint8_t v_kind_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___f_2674_; lean_object* v___x_2675_; 
lean_inc(v___y_2668_);
v___f_2674_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2674_, 0, v_k_2666_);
lean_closure_set(v___f_2674_, 1, v___y_2668_);
v___x_2675_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2663_, v_bi_2664_, v_type_2665_, v___f_2674_, v_kind_2667_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2675_) == 0)
{
return v___x_2675_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2663_ = stack[0].m_obj;
uint8_t v_bi_2664_ = stack[1].m_num;
lean_object* v_type_2665_ = stack[2].m_obj;
lean_object* v_k_2666_ = stack[3].m_obj;
uint8_t v_kind_2667_ = stack[4].m_num;
lean_object* v___y_2668_ = stack[5].m_obj;
lean_object* v___y_2669_ = stack[6].m_obj;
lean_object* v___y_2670_ = stack[7].m_obj;
lean_object* v___y_2671_ = stack[8].m_obj;
lean_object* v___y_2672_ = stack[9].m_obj;
lean_object* v_res_2684_;
v_res_2684_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2663_, v_bi_2664_, v_type_2665_, v_k_2666_, v_kind_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
stack->m_obj
 = v_res_2684_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2685_, lean_object* v_bi_2686_, lean_object* v_type_2687_, lean_object* v_k_2688_, lean_object* v_kind_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v_bi_boxed_2696_; uint8_t v_kind_boxed_2697_; lean_object* v_res_2698_; 
v_bi_boxed_2696_ = lean_unbox(v_bi_2686_);
v_kind_boxed_2697_ = lean_unbox(v_kind_2689_);
v_res_2698_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2685_, v_bi_boxed_2696_, v_type_2687_, v_k_2688_, v_kind_boxed_2697_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
return v_res_2698_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2699_);
return v___x_2705_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2699_ = stack[0].m_obj;
lean_object* v___y_2700_ = stack[1].m_obj;
lean_object* v___y_2701_ = stack[2].m_obj;
lean_object* v___y_2702_ = stack[3].m_obj;
lean_object* v___y_2703_ = stack[4].m_obj;
lean_object* v_res_2706_;
v_res_2706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
stack->m_obj
 = v_res_2706_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2713_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2714_, lean_object* v_type_2715_, lean_object* v_val_2716_, lean_object* v_k_2717_, uint8_t v_nondep_2718_, uint8_t v_kind_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___f_2726_; lean_object* v___x_2727_; 
lean_inc(v___y_2720_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2726_, 0, v_k_2717_);
lean_closure_set(v___f_2726_, 1, v___y_2720_);
v___x_2727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2714_, v_type_2715_, v_val_2716_, v___f_2726_, v_nondep_2718_, v_kind_2719_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2727_) == 0)
{
return v___x_2727_;
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2714_ = stack[0].m_obj;
lean_object* v_type_2715_ = stack[1].m_obj;
lean_object* v_val_2716_ = stack[2].m_obj;
lean_object* v_k_2717_ = stack[3].m_obj;
uint8_t v_nondep_2718_ = stack[4].m_num;
uint8_t v_kind_2719_ = stack[5].m_num;
lean_object* v___y_2720_ = stack[6].m_obj;
lean_object* v___y_2721_ = stack[7].m_obj;
lean_object* v___y_2722_ = stack[8].m_obj;
lean_object* v___y_2723_ = stack[9].m_obj;
lean_object* v___y_2724_ = stack[10].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2714_, v_type_2715_, v_val_2716_, v_k_2717_, v_nondep_2718_, v_kind_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2737_, lean_object* v_type_2738_, lean_object* v_val_2739_, lean_object* v_k_2740_, lean_object* v_nondep_2741_, lean_object* v_kind_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v_nondep_boxed_2749_; uint8_t v_kind_boxed_2750_; lean_object* v_res_2751_; 
v_nondep_boxed_2749_ = lean_unbox(v_nondep_2741_);
v_kind_boxed_2750_ = lean_unbox(v_kind_2742_);
v_res_2751_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2737_, v_type_2738_, v_val_2739_, v_k_2740_, v_nondep_boxed_2749_, v_kind_boxed_2750_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = l_Lean_maxRecDepthErrorMessage;
v___x_2758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2760_ = l_Lean_MessageData_ofFormat(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2762_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2763_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
lean_ctor_set(v___x_2763_, 1, v___x_2761_);
return v___x_2763_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2764_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_ref_2764_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2764_ = stack[0].m_obj;
lean_object* v_res_2769_;
v_res_2769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2764_);
stack->m_obj
 = v_res_2769_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2770_);
return v_res_2772_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___y_2781_; lean_object* v_toCold_2790_; lean_object* v_currRecDepth_2791_; lean_object* v_ref_2792_; uint16_t v_optionFlags_2793_; uint8_t v_suppressElabErrors_2794_; uint8_t v_isRecordingDeps_2795_; lean_object* v_maxRecDepth_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_toCold_2790_ = lean_ctor_get(v___y_2777_, 0);
v_currRecDepth_2791_ = lean_ctor_get(v___y_2777_, 1);
v_ref_2792_ = lean_ctor_get(v___y_2777_, 2);
v_optionFlags_2793_ = lean_ctor_get_uint16(v___y_2777_, sizeof(void*)*3);
v_suppressElabErrors_2794_ = lean_ctor_get_uint8(v___y_2777_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2795_ = lean_ctor_get_uint8(v___y_2777_, sizeof(void*)*3 + 3);
v_maxRecDepth_2801_ = lean_ctor_get(v_toCold_2790_, 3);
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = lean_nat_dec_eq(v_maxRecDepth_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_nat_dec_eq(v_currRecDepth_2791_, v_maxRecDepth_2801_);
if (v___x_2804_ == 0)
{
goto v___jp_2796_;
}
else
{
lean_object* v___x_2805_; 
lean_dec_ref(v_x_2773_);
lean_inc(v_ref_2792_);
v___x_2805_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2792_);
v___y_2781_ = v___x_2805_;
goto v___jp_2780_;
}
}
else
{
goto v___jp_2796_;
}
v___jp_2780_:
{
if (lean_obj_tag(v___y_2781_) == 0)
{
return v___y_2781_;
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___y_2781_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___y_2781_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___y_2781_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___y_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
v___jp_2796_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2797_ = lean_unsigned_to_nat(1u);
v___x_2798_ = lean_nat_add(v_currRecDepth_2791_, v___x_2797_);
lean_inc(v_ref_2792_);
lean_inc_ref(v_toCold_2790_);
v___x_2799_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2799_, 0, v_toCold_2790_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_ctor_set(v___x_2799_, 2, v_ref_2792_);
lean_ctor_set_uint16(v___x_2799_, sizeof(void*)*3, v_optionFlags_2793_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*3 + 2, v_suppressElabErrors_2794_);
lean_ctor_set_uint8(v___x_2799_, sizeof(void*)*3 + 3, v_isRecordingDeps_2795_);
lean_inc(v___y_2778_);
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v___y_2774_);
v___x_2800_ = lean_apply_6(v_x_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___x_2799_, v___y_2778_, lean_box(0));
v___y_2781_ = v___x_2800_;
goto v___jp_2780_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2773_ = stack[0].m_obj;
lean_object* v___y_2774_ = stack[1].m_obj;
lean_object* v___y_2775_ = stack[2].m_obj;
lean_object* v___y_2776_ = stack[3].m_obj;
lean_object* v___y_2777_ = stack[4].m_obj;
lean_object* v___y_2778_ = stack[5].m_obj;
lean_object* v_res_2806_;
v_res_2806_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
stack->m_obj
 = v_res_2806_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2815_, lean_object* v_pre_2816_, lean_object* v_post_2817_, lean_object* v_usedLetOnly_2818_, lean_object* v_skipConstInApp_2819_, lean_object* v_skipInstances_2820_, lean_object* v_body_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v_usedLetOnly_boxed_2829_; uint8_t v_skipConstInApp_boxed_2830_; uint8_t v_skipInstances_boxed_2831_; lean_object* v_res_2832_; 
v_usedLetOnly_boxed_2829_ = lean_unbox(v_usedLetOnly_2818_);
v_skipConstInApp_boxed_2830_ = lean_unbox(v_skipConstInApp_2819_);
v_skipInstances_boxed_2831_ = lean_unbox(v_skipInstances_2820_);
v_res_2832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2815_, v_pre_2816_, v_post_2817_, v_usedLetOnly_boxed_2829_, v_skipConstInApp_boxed_2830_, v_skipInstances_boxed_2831_, v_body_2821_, v_x_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
return v_res_2832_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2836_, lean_object* v_pre_2837_, lean_object* v_post_2838_, uint8_t v_usedLetOnly_2839_, uint8_t v_skipConstInApp_2840_, uint8_t v_skipInstances_2841_, lean_object* v_body_2842_, lean_object* v_x_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_array_push(v_fvars_2836_, v_x_2843_);
v___x_2851_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2837_, v_post_2838_, v_usedLetOnly_2839_, v_skipConstInApp_2840_, v_skipInstances_2841_, v___x_2850_, v_body_2842_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
return v___x_2851_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2836_ = stack[0].m_obj;
lean_object* v_pre_2837_ = stack[1].m_obj;
lean_object* v_post_2838_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2839_ = stack[3].m_num;
uint8_t v_skipConstInApp_2840_ = stack[4].m_num;
uint8_t v_skipInstances_2841_ = stack[5].m_num;
lean_object* v_body_2842_ = stack[6].m_obj;
lean_object* v_x_2843_ = stack[7].m_obj;
lean_object* v___y_2844_ = stack[8].m_obj;
lean_object* v___y_2845_ = stack[9].m_obj;
lean_object* v___y_2846_ = stack[10].m_obj;
lean_object* v___y_2847_ = stack[11].m_obj;
lean_object* v___y_2848_ = stack[12].m_obj;
lean_object* v_res_2852_;
v_res_2852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2836_, v_pre_2837_, v_post_2838_, v_usedLetOnly_2839_, v_skipConstInApp_2840_, v_skipInstances_2841_, v_body_2842_, v_x_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
stack->m_obj
 = v_res_2852_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2853_, lean_object* v_pre_2854_, lean_object* v_post_2855_, lean_object* v_usedLetOnly_2856_, lean_object* v_skipConstInApp_2857_, lean_object* v_skipInstances_2858_, lean_object* v_body_2859_, lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_usedLetOnly_boxed_2867_; uint8_t v_skipConstInApp_boxed_2868_; uint8_t v_skipInstances_boxed_2869_; lean_object* v_res_2870_; 
v_usedLetOnly_boxed_2867_ = lean_unbox(v_usedLetOnly_2856_);
v_skipConstInApp_boxed_2868_ = lean_unbox(v_skipConstInApp_2857_);
v_skipInstances_boxed_2869_ = lean_unbox(v_skipInstances_2858_);
v_res_2870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2853_, v_pre_2854_, v_post_2855_, v_usedLetOnly_boxed_2867_, v_skipConstInApp_boxed_2868_, v_skipInstances_boxed_2869_, v_body_2859_, v_x_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
return v_res_2870_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2871_, lean_object* v_post_2872_, uint8_t v_usedLetOnly_2873_, uint8_t v_skipConstInApp_2874_, uint8_t v_skipInstances_2875_, lean_object* v_e_2876_, lean_object* v_a_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; 
lean_inc_ref(v_post_2872_);
lean_inc(v___y_2881_);
lean_inc_ref(v___y_2880_);
lean_inc(v___y_2879_);
lean_inc_ref(v___y_2878_);
lean_inc_ref(v_e_2876_);
v___x_2883_ = lean_apply_6(v_post_2872_, v_e_2876_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, lean_box(0));
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2902_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2902_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2902_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
switch(lean_obj_tag(v_a_2884_))
{
case 0:
{
lean_object* v_e_2888_; lean_object* v___x_2890_; 
lean_dec_ref(v_e_2876_);
lean_dec_ref(v_post_2872_);
lean_dec_ref(v_pre_2871_);
v_e_2888_ = lean_ctor_get(v_a_2884_, 0);
lean_inc_ref(v_e_2888_);
lean_dec_ref_known(v_a_2884_, 1);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_e_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_e_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
case 1:
{
lean_object* v_e_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2886_);
lean_dec_ref(v_e_2876_);
v_e_2892_ = lean_ctor_get(v_a_2884_, 0);
lean_inc_ref(v_e_2892_);
lean_dec_ref_known(v_a_2884_, 1);
v___x_2893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2871_, v_post_2872_, v_usedLetOnly_2873_, v_skipConstInApp_2874_, v_skipInstances_2875_, v_e_2892_, v_a_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
return v___x_2893_;
}
default: 
{
lean_object* v_e_x3f_2894_; 
lean_dec_ref(v_post_2872_);
lean_dec_ref(v_pre_2871_);
v_e_x3f_2894_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_e_x3f_2894_);
lean_dec_ref_known(v_a_2884_, 1);
if (lean_obj_tag(v_e_x3f_2894_) == 0)
{
lean_object* v___x_2896_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_e_2876_);
v___x_2896_ = v___x_2886_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_e_2876_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
else
{
lean_object* v_val_2898_; lean_object* v___x_2900_; 
lean_dec_ref(v_e_2876_);
v_val_2898_ = lean_ctor_get(v_e_x3f_2894_, 0);
lean_inc(v_val_2898_);
lean_dec_ref_known(v_e_x3f_2894_, 1);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v_val_2898_);
v___x_2900_ = v___x_2886_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_val_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v_e_2876_);
lean_dec_ref(v_post_2872_);
lean_dec_ref(v_pre_2871_);
v_a_2903_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2883_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2883_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2871_ = stack[0].m_obj;
lean_object* v_post_2872_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2873_ = stack[2].m_num;
uint8_t v_skipConstInApp_2874_ = stack[3].m_num;
uint8_t v_skipInstances_2875_ = stack[4].m_num;
lean_object* v_e_2876_ = stack[5].m_obj;
lean_object* v_a_2877_ = stack[6].m_obj;
lean_object* v___y_2878_ = stack[7].m_obj;
lean_object* v___y_2879_ = stack[8].m_obj;
lean_object* v___y_2880_ = stack[9].m_obj;
lean_object* v___y_2881_ = stack[10].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2871_, v_post_2872_, v_usedLetOnly_2873_, v_skipConstInApp_2874_, v_skipInstances_2875_, v_e_2876_, v_a_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
stack->m_obj
 = v_res_2911_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2912_, lean_object* v_post_2913_, uint8_t v_usedLetOnly_2914_, uint8_t v_skipConstInApp_2915_, uint8_t v_skipInstances_2916_, lean_object* v_fvars_2917_, lean_object* v_e_2918_, lean_object* v_a_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
if (lean_obj_tag(v_e_2918_) == 6)
{
lean_object* v_binderName_2925_; lean_object* v_binderType_2926_; lean_object* v_body_2927_; uint8_t v_binderInfo_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___f_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_binderName_2925_ = lean_ctor_get(v_e_2918_, 0);
lean_inc(v_binderName_2925_);
v_binderType_2926_ = lean_ctor_get(v_e_2918_, 1);
lean_inc_ref(v_binderType_2926_);
v_body_2927_ = lean_ctor_get(v_e_2918_, 2);
lean_inc_ref(v_body_2927_);
v_binderInfo_2928_ = lean_ctor_get_uint8(v_e_2918_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2918_, 3);
v___x_2929_ = lean_box(v_usedLetOnly_2914_);
v___x_2930_ = lean_box(v_skipConstInApp_2915_);
v___x_2931_ = lean_box(v_skipInstances_2916_);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
lean_inc_ref(v_fvars_2917_);
v___f_2932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2932_, 0, v_fvars_2917_);
lean_closure_set(v___f_2932_, 1, v_pre_2912_);
lean_closure_set(v___f_2932_, 2, v_post_2913_);
lean_closure_set(v___f_2932_, 3, v___x_2929_);
lean_closure_set(v___f_2932_, 4, v___x_2930_);
lean_closure_set(v___f_2932_, 5, v___x_2931_);
lean_closure_set(v___f_2932_, 6, v_body_2927_);
v___x_2933_ = lean_expr_instantiate_rev(v_binderType_2926_, v_fvars_2917_);
lean_dec_ref(v_fvars_2917_);
lean_dec_ref(v_binderType_2926_);
v___x_2934_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v___x_2933_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = 0;
v___x_2937_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2925_, v_binderInfo_2928_, v_a_2935_, v___f_2932_, v___x_2936_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2937_;
}
else
{
lean_dec_ref(v___f_2932_);
lean_dec(v_binderName_2925_);
return v___x_2934_;
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_expr_instantiate_rev(v_e_2918_, v_fvars_2917_);
lean_dec_ref(v_e_2918_);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v___x_2938_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; uint8_t v___x_2941_; uint8_t v___x_2942_; uint8_t v___x_2943_; lean_object* v___x_2944_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = 0;
v___x_2942_ = 1;
v___x_2943_ = 1;
v___x_2944_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2917_, v_a_2940_, v___x_2941_, v_usedLetOnly_2914_, v___x_2941_, v___x_2942_, v___x_2943_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec_ref(v_fvars_2917_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2946_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v___x_2946_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v_a_2945_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2946_;
}
else
{
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2944_;
}
}
else
{
lean_dec_ref(v_fvars_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2939_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2912_ = stack[0].m_obj;
lean_object* v_post_2913_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2914_ = stack[2].m_num;
uint8_t v_skipConstInApp_2915_ = stack[3].m_num;
uint8_t v_skipInstances_2916_ = stack[4].m_num;
lean_object* v_fvars_2917_ = stack[5].m_obj;
lean_object* v_e_2918_ = stack[6].m_obj;
lean_object* v_a_2919_ = stack[7].m_obj;
lean_object* v___y_2920_ = stack[8].m_obj;
lean_object* v___y_2921_ = stack[9].m_obj;
lean_object* v___y_2922_ = stack[10].m_obj;
lean_object* v___y_2923_ = stack[11].m_obj;
lean_object* v_res_2947_;
v_res_2947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v_fvars_2917_, v_e_2918_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
stack->m_obj
 = v_res_2947_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2948_, lean_object* v_pre_2949_, lean_object* v_post_2950_, uint8_t v_usedLetOnly_2951_, uint8_t v_skipConstInApp_2952_, uint8_t v_skipInstances_2953_, lean_object* v_body_2954_, lean_object* v_x_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_array_push(v_fvars_2948_, v_x_2955_);
v___x_2963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2949_, v_post_2950_, v_usedLetOnly_2951_, v_skipConstInApp_2952_, v_skipInstances_2953_, v___x_2962_, v_body_2954_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2963_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2948_ = stack[0].m_obj;
lean_object* v_pre_2949_ = stack[1].m_obj;
lean_object* v_post_2950_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2951_ = stack[3].m_num;
uint8_t v_skipConstInApp_2952_ = stack[4].m_num;
uint8_t v_skipInstances_2953_ = stack[5].m_num;
lean_object* v_body_2954_ = stack[6].m_obj;
lean_object* v_x_2955_ = stack[7].m_obj;
lean_object* v___y_2956_ = stack[8].m_obj;
lean_object* v___y_2957_ = stack[9].m_obj;
lean_object* v___y_2958_ = stack[10].m_obj;
lean_object* v___y_2959_ = stack[11].m_obj;
lean_object* v___y_2960_ = stack[12].m_obj;
lean_object* v_res_2964_;
v_res_2964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2948_, v_pre_2949_, v_post_2950_, v_usedLetOnly_2951_, v_skipConstInApp_2952_, v_skipInstances_2953_, v_body_2954_, v_x_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
stack->m_obj
 = v_res_2964_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2965_, lean_object* v_pre_2966_, lean_object* v_post_2967_, lean_object* v_usedLetOnly_2968_, lean_object* v_skipConstInApp_2969_, lean_object* v_skipInstances_2970_, lean_object* v_body_2971_, lean_object* v_x_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v_usedLetOnly_boxed_2979_; uint8_t v_skipConstInApp_boxed_2980_; uint8_t v_skipInstances_boxed_2981_; lean_object* v_res_2982_; 
v_usedLetOnly_boxed_2979_ = lean_unbox(v_usedLetOnly_2968_);
v_skipConstInApp_boxed_2980_ = lean_unbox(v_skipConstInApp_2969_);
v_skipInstances_boxed_2981_ = lean_unbox(v_skipInstances_2970_);
v_res_2982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2965_, v_pre_2966_, v_post_2967_, v_usedLetOnly_boxed_2979_, v_skipConstInApp_boxed_2980_, v_skipInstances_boxed_2981_, v_body_2971_, v_x_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
return v_res_2982_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2983_, lean_object* v_post_2984_, uint8_t v_usedLetOnly_2985_, uint8_t v_skipConstInApp_2986_, uint8_t v_skipInstances_2987_, lean_object* v_fvars_2988_, lean_object* v_e_2989_, lean_object* v_a_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
if (lean_obj_tag(v_e_2989_) == 8)
{
lean_object* v_declName_2996_; lean_object* v_type_2997_; lean_object* v_value_2998_; lean_object* v_body_2999_; uint8_t v_nondep_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_declName_2996_ = lean_ctor_get(v_e_2989_, 0);
lean_inc(v_declName_2996_);
v_type_2997_ = lean_ctor_get(v_e_2989_, 1);
lean_inc_ref(v_type_2997_);
v_value_2998_ = lean_ctor_get(v_e_2989_, 2);
lean_inc_ref(v_value_2998_);
v_body_2999_ = lean_ctor_get(v_e_2989_, 3);
lean_inc_ref(v_body_2999_);
v_nondep_3000_ = lean_ctor_get_uint8(v_e_2989_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2989_, 4);
v___x_3001_ = lean_box(v_usedLetOnly_2985_);
v___x_3002_ = lean_box(v_skipConstInApp_2986_);
v___x_3003_ = lean_box(v_skipInstances_2987_);
lean_inc_ref_n(v_post_2984_, 2);
lean_inc_ref_n(v_pre_2983_, 2);
lean_inc_ref(v_fvars_2988_);
v___f_3004_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3004_, 0, v_fvars_2988_);
lean_closure_set(v___f_3004_, 1, v_pre_2983_);
lean_closure_set(v___f_3004_, 2, v_post_2984_);
lean_closure_set(v___f_3004_, 3, v___x_3001_);
lean_closure_set(v___f_3004_, 4, v___x_3002_);
lean_closure_set(v___f_3004_, 5, v___x_3003_);
lean_closure_set(v___f_3004_, 6, v_body_2999_);
v___x_3005_ = lean_expr_instantiate_rev(v_type_2997_, v_fvars_2988_);
lean_dec_ref(v_type_2997_);
v___x_3006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v___x_3005_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = lean_expr_instantiate_rev(v_value_2998_, v_fvars_2988_);
lean_dec_ref(v_fvars_2988_);
lean_dec_ref(v_value_2998_);
v___x_3009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v___x_3008_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = 0;
v___x_3012_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2996_, v_a_3007_, v_a_3010_, v___f_3004_, v_nondep_3000_, v___x_3011_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
return v___x_3012_;
}
else
{
lean_dec(v_a_3007_);
lean_dec_ref(v___f_3004_);
lean_dec(v_declName_2996_);
return v___x_3009_;
}
}
else
{
lean_dec_ref(v___f_3004_);
lean_dec_ref(v_value_2998_);
lean_dec(v_declName_2996_);
lean_dec_ref(v_fvars_2988_);
lean_dec_ref(v_post_2984_);
lean_dec_ref(v_pre_2983_);
return v___x_3006_;
}
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_expr_instantiate_rev(v_e_2989_, v_fvars_2988_);
lean_dec_ref(v_e_2989_);
lean_inc_ref(v_post_2984_);
lean_inc_ref(v_pre_2983_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v___x_3013_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; uint8_t v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = 0;
v___x_3017_ = 1;
v___x_3018_ = l_Lean_Meta_mkLetFVars(v_fvars_2988_, v_a_3015_, v_usedLetOnly_2985_, v___x_3016_, v___x_3017_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec_ref(v_fvars_2988_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v_a_3019_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
return v___x_3020_;
}
else
{
lean_dec_ref(v_post_2984_);
lean_dec_ref(v_pre_2983_);
return v___x_3018_;
}
}
else
{
lean_dec_ref(v_fvars_2988_);
lean_dec_ref(v_post_2984_);
lean_dec_ref(v_pre_2983_);
return v___x_3014_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2983_ = stack[0].m_obj;
lean_object* v_post_2984_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2985_ = stack[2].m_num;
uint8_t v_skipConstInApp_2986_ = stack[3].m_num;
uint8_t v_skipInstances_2987_ = stack[4].m_num;
lean_object* v_fvars_2988_ = stack[5].m_obj;
lean_object* v_e_2989_ = stack[6].m_obj;
lean_object* v_a_2990_ = stack[7].m_obj;
lean_object* v___y_2991_ = stack[8].m_obj;
lean_object* v___y_2992_ = stack[9].m_obj;
lean_object* v___y_2993_ = stack[10].m_obj;
lean_object* v___y_2994_ = stack[11].m_obj;
lean_object* v_res_3021_;
v_res_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v_fvars_2988_, v_e_2989_, v_a_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
stack->m_obj
 = v_res_3021_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_3022_, lean_object* v_post_3023_, uint8_t v_usedLetOnly_3024_, uint8_t v_skipConstInApp_3025_, uint8_t v_skipInstances_3026_, size_t v_sz_3027_, size_t v_i_3028_, lean_object* v_bs_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_lt(v_i_3028_, v_sz_3027_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
lean_dec_ref(v_post_3023_);
lean_dec_ref(v_pre_3022_);
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_bs_3029_);
return v___x_3037_;
}
else
{
lean_object* v_v_3038_; lean_object* v___x_3039_; lean_object* v_bs_x27_3040_; lean_object* v___x_3041_; 
v_v_3038_ = lean_array_uget(v_bs_3029_, v_i_3028_);
v___x_3039_ = lean_unsigned_to_nat(0u);
v_bs_x27_3040_ = lean_array_uset(v_bs_3029_, v_i_3028_, v___x_3039_);
lean_inc_ref(v_post_3023_);
lean_inc_ref(v_pre_3022_);
v___x_3041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3022_, v_post_3023_, v_usedLetOnly_3024_, v_skipConstInApp_3025_, v_skipInstances_3026_, v_v_3038_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_add(v_i_3028_, v___x_3043_);
v___x_3045_ = lean_array_uset(v_bs_x27_3040_, v_i_3028_, v_a_3042_);
v_i_3028_ = v___x_3044_;
v_bs_3029_ = v___x_3045_;
goto _start;
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_bs_x27_3040_);
lean_dec_ref(v_post_3023_);
lean_dec_ref(v_pre_3022_);
v_a_3047_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3041_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3041_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3022_ = stack[0].m_obj;
lean_object* v_post_3023_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3024_ = stack[2].m_num;
uint8_t v_skipConstInApp_3025_ = stack[3].m_num;
uint8_t v_skipInstances_3026_ = stack[4].m_num;
size_t v_sz_3027_ = stack[5].m_num;
size_t v_i_3028_ = stack[6].m_num;
lean_object* v_bs_3029_ = stack[7].m_obj;
lean_object* v___y_3030_ = stack[8].m_obj;
lean_object* v___y_3031_ = stack[9].m_obj;
lean_object* v___y_3032_ = stack[10].m_obj;
lean_object* v___y_3033_ = stack[11].m_obj;
lean_object* v___y_3034_ = stack[12].m_obj;
lean_object* v_res_3055_;
v_res_3055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3022_, v_post_3023_, v_usedLetOnly_3024_, v_skipConstInApp_3025_, v_skipInstances_3026_, v_sz_3027_, v_i_3028_, v_bs_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
stack->m_obj
 = v_res_3055_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3056_, lean_object* v_post_3057_, uint8_t v_usedLetOnly_3058_, uint8_t v_skipConstInApp_3059_, uint8_t v_skipInstances_3060_, lean_object* v___x_3061_, lean_object* v___y_3062_, lean_object* v_b_3063_, lean_object* v_a_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3056_, v_post_3057_, v_usedLetOnly_3058_, v_skipConstInApp_3059_, v_skipInstances_3060_, v___x_3061_, v___y_3062_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3080_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3080_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3080_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3075_ = lean_array_fset(v_b_3063_, v_a_3064_, v_a_3071_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3076_);
v___x_3078_ = v___x_3073_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v_b_3063_);
v_a_3081_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3070_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3070_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3056_ = stack[0].m_obj;
lean_object* v_post_3057_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3058_ = stack[2].m_num;
uint8_t v_skipConstInApp_3059_ = stack[3].m_num;
uint8_t v_skipInstances_3060_ = stack[4].m_num;
lean_object* v___x_3061_ = stack[5].m_obj;
lean_object* v___y_3062_ = stack[6].m_obj;
lean_object* v_b_3063_ = stack[7].m_obj;
lean_object* v_a_3064_ = stack[8].m_obj;
lean_object* v___y_3065_ = stack[9].m_obj;
lean_object* v___y_3066_ = stack[10].m_obj;
lean_object* v___y_3067_ = stack[11].m_obj;
lean_object* v___y_3068_ = stack[12].m_obj;
lean_object* v_res_3089_;
v_res_3089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3056_, v_post_3057_, v_usedLetOnly_3058_, v_skipConstInApp_3059_, v_skipInstances_3060_, v___x_3061_, v___y_3062_, v_b_3063_, v_a_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
stack->m_obj
 = v_res_3089_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3090_, lean_object* v_post_3091_, lean_object* v_usedLetOnly_3092_, lean_object* v_skipConstInApp_3093_, lean_object* v_skipInstances_3094_, lean_object* v___x_3095_, lean_object* v___y_3096_, lean_object* v_b_3097_, lean_object* v_a_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
uint8_t v_usedLetOnly_boxed_3104_; uint8_t v_skipConstInApp_boxed_3105_; uint8_t v_skipInstances_boxed_3106_; lean_object* v_res_3107_; 
v_usedLetOnly_boxed_3104_ = lean_unbox(v_usedLetOnly_3092_);
v_skipConstInApp_boxed_3105_ = lean_unbox(v_skipConstInApp_3093_);
v_skipInstances_boxed_3106_ = lean_unbox(v_skipInstances_3094_);
v_res_3107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3090_, v_post_3091_, v_usedLetOnly_boxed_3104_, v_skipConstInApp_boxed_3105_, v_skipInstances_boxed_3106_, v___x_3095_, v___y_3096_, v_b_3097_, v_a_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v_a_3098_);
lean_dec(v___y_3096_);
return v_res_3107_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3108_, lean_object* v___x_3109_, lean_object* v_pre_3110_, lean_object* v_post_3111_, uint8_t v_usedLetOnly_3112_, uint8_t v_skipConstInApp_3113_, uint8_t v_skipInstances_3114_, lean_object* v_a_3115_, lean_object* v_b_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___y_3124_; uint8_t v___x_3147_; 
v___x_3147_ = lean_nat_dec_lt(v_a_3115_, v_upperBound_3108_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
lean_dec(v_a_3115_);
lean_dec_ref(v_post_3111_);
lean_dec_ref(v_pre_3110_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3116_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3149_ = lean_array_fget_borrowed(v_b_3116_, v_a_3115_);
v___x_3150_ = lean_array_get_size(v___x_3109_);
v___x_3151_ = lean_nat_dec_lt(v_a_3115_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; 
lean_inc(v___x_3149_);
v___x_3152_ = lean_box(v_usedLetOnly_3112_);
v___x_3153_ = lean_box(v_skipConstInApp_3113_);
v___x_3154_ = lean_box(v_skipInstances_3114_);
lean_inc(v_a_3115_);
lean_inc(v___y_3117_);
lean_inc_ref(v_post_3111_);
lean_inc_ref(v_pre_3110_);
v___f_3155_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3155_, 0, v_pre_3110_);
lean_closure_set(v___f_3155_, 1, v_post_3111_);
lean_closure_set(v___f_3155_, 2, v___x_3152_);
lean_closure_set(v___f_3155_, 3, v___x_3153_);
lean_closure_set(v___f_3155_, 4, v___x_3154_);
lean_closure_set(v___f_3155_, 5, v___x_3149_);
lean_closure_set(v___f_3155_, 6, v___y_3117_);
lean_closure_set(v___f_3155_, 7, v_b_3116_);
lean_closure_set(v___f_3155_, 8, v_a_3115_);
v___y_3124_ = v___f_3155_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3156_; uint8_t v_isInstance_3157_; 
v___x_3156_ = lean_array_fget_borrowed(v___x_3109_, v_a_3115_);
v_isInstance_3157_ = lean_ctor_get_uint8(v___x_3156_, sizeof(void*)*1 + 4);
if (v_isInstance_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___f_3161_; 
lean_inc(v___x_3149_);
v___x_3158_ = lean_box(v_usedLetOnly_3112_);
v___x_3159_ = lean_box(v_skipConstInApp_3113_);
v___x_3160_ = lean_box(v_skipInstances_3114_);
lean_inc(v_a_3115_);
lean_inc(v___y_3117_);
lean_inc_ref(v_post_3111_);
lean_inc_ref(v_pre_3110_);
v___f_3161_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3161_, 0, v_pre_3110_);
lean_closure_set(v___f_3161_, 1, v_post_3111_);
lean_closure_set(v___f_3161_, 2, v___x_3158_);
lean_closure_set(v___f_3161_, 3, v___x_3159_);
lean_closure_set(v___f_3161_, 4, v___x_3160_);
lean_closure_set(v___f_3161_, 5, v___x_3149_);
lean_closure_set(v___f_3161_, 6, v___y_3117_);
lean_closure_set(v___f_3161_, 7, v_b_3116_);
lean_closure_set(v___f_3161_, 8, v_a_3115_);
v___y_3124_ = v___f_3161_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3162_; lean_object* v___f_3163_; 
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_b_3116_);
v___f_3163_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3163_, 0, v___x_3162_);
v___y_3124_ = v___f_3163_;
goto v___jp_3123_;
}
}
}
v___jp_3123_:
{
lean_object* v___x_3125_; 
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
lean_inc(v___y_3119_);
lean_inc_ref(v___y_3118_);
v___x_3125_ = lean_apply_5(v___y_3124_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, lean_box(0));
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3138_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3138_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
if (lean_obj_tag(v_a_3126_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; 
lean_dec(v_a_3115_);
lean_dec_ref(v_post_3111_);
lean_dec_ref(v_pre_3110_);
v_a_3130_ = lean_ctor_get(v_a_3126_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v_a_3126_, 1);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v_a_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_del_object(v___x_3128_);
v_a_3134_ = lean_ctor_get(v_a_3126_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v_a_3126_, 1);
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_add(v_a_3115_, v___x_3135_);
lean_dec(v_a_3115_);
v_a_3115_ = v___x_3136_;
v_b_3116_ = v_a_3134_;
goto _start;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_a_3115_);
lean_dec_ref(v_post_3111_);
lean_dec_ref(v_pre_3110_);
v_a_3139_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3125_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3125_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3108_ = stack[0].m_obj;
lean_object* v___x_3109_ = stack[1].m_obj;
lean_object* v_pre_3110_ = stack[2].m_obj;
lean_object* v_post_3111_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3112_ = stack[4].m_num;
uint8_t v_skipConstInApp_3113_ = stack[5].m_num;
uint8_t v_skipInstances_3114_ = stack[6].m_num;
lean_object* v_a_3115_ = stack[7].m_obj;
lean_object* v_b_3116_ = stack[8].m_obj;
lean_object* v___y_3117_ = stack[9].m_obj;
lean_object* v___y_3118_ = stack[10].m_obj;
lean_object* v___y_3119_ = stack[11].m_obj;
lean_object* v___y_3120_ = stack[12].m_obj;
lean_object* v___y_3121_ = stack[13].m_obj;
lean_object* v_res_3164_;
v_res_3164_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3108_, v___x_3109_, v_pre_3110_, v_post_3111_, v_usedLetOnly_3112_, v_skipConstInApp_3113_, v_skipInstances_3114_, v_a_3115_, v_b_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
stack->m_obj
 = v_res_3164_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3165_, lean_object* v_pre_3166_, lean_object* v_post_3167_, uint8_t v_usedLetOnly_3168_, uint8_t v_skipConstInApp_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_f_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; 
if (lean_obj_tag(v_x_3170_) == 5)
{
lean_object* v_fn_3228_; lean_object* v_arg_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_fn_3228_ = lean_ctor_get(v_x_3170_, 0);
lean_inc_ref(v_fn_3228_);
v_arg_3229_ = lean_ctor_get(v_x_3170_, 1);
lean_inc_ref(v_arg_3229_);
lean_dec_ref_known(v_x_3170_, 2);
v___x_3230_ = lean_array_set(v_x_3171_, v_x_3172_, v_arg_3229_);
v___x_3231_ = lean_unsigned_to_nat(1u);
v___x_3232_ = lean_nat_sub(v_x_3172_, v___x_3231_);
lean_dec(v_x_3172_);
v_x_3170_ = v_fn_3228_;
v_x_3171_ = v___x_3230_;
v_x_3172_ = v___x_3232_;
goto _start;
}
else
{
lean_dec(v_x_3172_);
if (v_skipConstInApp_3169_ == 0)
{
goto v___jp_3225_;
}
else
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_Expr_isConst(v_x_3170_);
if (v___x_3234_ == 0)
{
goto v___jp_3225_;
}
else
{
v_f_3180_ = v_x_3170_;
v___y_3181_ = v___y_3173_;
v___y_3182_ = v___y_3174_;
v___y_3183_ = v___y_3175_;
v___y_3184_ = v___y_3176_;
v___y_3185_ = v___y_3177_;
goto v___jp_3179_;
}
}
}
v___jp_3179_:
{
if (v_skipInstances_3165_ == 0)
{
size_t v_sz_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v_sz_3186_ = lean_array_size(v_x_3171_);
v___x_3187_ = ((size_t)0ULL);
lean_inc_ref(v_post_3167_);
lean_inc_ref(v_pre_3166_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3165_, v_sz_3186_, v___x_3187_, v_x_3171_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = l_Lean_mkAppN(v_f_3180_, v_a_3189_);
lean_dec(v_a_3189_);
v___x_3191_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3165_, v___x_3190_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3191_;
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v_f_3180_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
v_a_3192_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3188_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3188_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_array_get_size(v_x_3171_);
lean_inc_ref(v_f_3180_);
v___x_3201_ = l_Lean_Meta_getFunInfoNArgs(v_f_3180_, v___x_3200_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v_paramInfo_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v_paramInfo_3203_ = lean_ctor_get(v_a_3202_, 0);
lean_inc_ref(v_paramInfo_3203_);
lean_dec(v_a_3202_);
v___x_3204_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3167_);
lean_inc_ref(v_pre_3166_);
v___x_3205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3200_, v_paramInfo_3203_, v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3165_, v___x_3204_, v_x_3171_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec_ref(v_paramInfo_3203_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v___x_3207_ = l_Lean_mkAppN(v_f_3180_, v_a_3206_);
lean_dec(v_a_3206_);
v___x_3208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3165_, v___x_3207_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3208_;
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v_f_3180_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
v_a_3209_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3205_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3205_);
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
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v_f_3180_);
lean_dec_ref(v_x_3171_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
v_a_3217_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3201_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3201_);
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
}
v___jp_3225_:
{
lean_object* v___x_3226_; 
lean_inc_ref(v_post_3167_);
lean_inc_ref(v_pre_3166_);
v___x_3226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3165_, v_x_3170_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v_f_3180_ = v_a_3227_;
v___y_3181_ = v___y_3173_;
v___y_3182_ = v___y_3174_;
v___y_3183_ = v___y_3175_;
v___y_3184_ = v___y_3176_;
v___y_3185_ = v___y_3177_;
goto v___jp_3179_;
}
else
{
lean_dec_ref(v_x_3171_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
return v___x_3226_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_3165_ = stack[0].m_num;
lean_object* v_pre_3166_ = stack[1].m_obj;
lean_object* v_post_3167_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3168_ = stack[3].m_num;
uint8_t v_skipConstInApp_3169_ = stack[4].m_num;
lean_object* v_x_3170_ = stack[5].m_obj;
lean_object* v_x_3171_ = stack[6].m_obj;
lean_object* v_x_3172_ = stack[7].m_obj;
lean_object* v___y_3173_ = stack[8].m_obj;
lean_object* v___y_3174_ = stack[9].m_obj;
lean_object* v___y_3175_ = stack[10].m_obj;
lean_object* v___y_3176_ = stack[11].m_obj;
lean_object* v___y_3177_ = stack[12].m_obj;
lean_object* v_res_3235_;
v_res_3235_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3165_, v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_x_3170_, v_x_3171_, v_x_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
stack->m_obj
 = v_res_3235_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3236_, lean_object* v_pre_3237_, lean_object* v_e_3238_, lean_object* v_post_3239_, uint8_t v_usedLetOnly_3240_, uint8_t v_skipConstInApp_3241_, uint8_t v_skipInstances_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Core_checkSystem(v___x_3236_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref_known(v___x_3249_, 1);
lean_inc_ref(v_pre_3237_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc_ref(v_e_3238_);
v___x_3250_ = lean_apply_6(v_pre_3237_, v_e_3238_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3299_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3299_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3299_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___y_3256_; 
switch(lean_obj_tag(v_a_3251_))
{
case 0:
{
lean_object* v_e_3291_; lean_object* v___x_3293_; 
lean_dec_ref(v_post_3239_);
lean_dec_ref(v_e_3238_);
lean_dec_ref(v_pre_3237_);
v_e_3291_ = lean_ctor_get(v_a_3251_, 0);
lean_inc_ref(v_e_3291_);
lean_dec_ref_known(v_a_3251_, 1);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v_e_3291_);
v___x_3293_ = v___x_3253_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_e_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
case 1:
{
lean_object* v_e_3295_; lean_object* v___x_3296_; 
lean_del_object(v___x_3253_);
lean_dec_ref(v_e_3238_);
v_e_3295_ = lean_ctor_get(v_a_3251_, 0);
lean_inc_ref(v_e_3295_);
lean_dec_ref_known(v_a_3251_, 1);
v___x_3296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v_e_3295_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3296_;
}
default: 
{
lean_object* v_e_x3f_3297_; 
lean_del_object(v___x_3253_);
v_e_x3f_3297_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_e_x3f_3297_);
lean_dec_ref_known(v_a_3251_, 1);
if (lean_obj_tag(v_e_x3f_3297_) == 0)
{
v___y_3256_ = v_e_3238_;
goto v___jp_3255_;
}
else
{
lean_object* v_val_3298_; 
lean_dec_ref(v_e_3238_);
v_val_3298_ = lean_ctor_get(v_e_x3f_3297_, 0);
lean_inc(v_val_3298_);
lean_dec_ref_known(v_e_x3f_3297_, 1);
v___y_3256_ = v_val_3298_;
goto v___jp_3255_;
}
}
}
v___jp_3255_:
{
switch(lean_obj_tag(v___y_3256_))
{
case 7:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___x_3257_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3258_;
}
case 6:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___x_3259_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3260_;
}
case 8:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___x_3261_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3262_;
}
case 5:
{
lean_object* v_dummy_3263_; lean_object* v_nargs_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_dummy_3263_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3264_ = l_Lean_Expr_getAppNumArgs(v___y_3256_);
lean_inc(v_nargs_3264_);
v___x_3265_ = lean_mk_array(v_nargs_3264_, v_dummy_3263_);
v___x_3266_ = lean_unsigned_to_nat(1u);
v___x_3267_ = lean_nat_sub(v_nargs_3264_, v___x_3266_);
lean_dec(v_nargs_3264_);
v___x_3268_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3242_, v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v___y_3256_, v___x_3265_, v___x_3267_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3268_;
}
case 10:
{
lean_object* v_data_3269_; lean_object* v_expr_3270_; lean_object* v___x_3271_; 
v_data_3269_ = lean_ctor_get(v___y_3256_, 0);
v_expr_3270_ = lean_ctor_get(v___y_3256_, 1);
lean_inc_ref(v_expr_3270_);
lean_inc_ref(v_post_3239_);
lean_inc_ref(v_pre_3237_);
v___x_3271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v_expr_3270_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; size_t v___x_3273_; size_t v___x_3274_; uint8_t v___x_3275_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = lean_ptr_addr(v_expr_3270_);
v___x_3274_ = lean_ptr_addr(v_a_3272_);
v___x_3275_ = lean_usize_dec_eq(v___x_3273_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_inc(v_data_3269_);
lean_dec_ref_known(v___y_3256_, 2);
v___x_3276_ = l_Lean_Expr_mdata___override(v_data_3269_, v_a_3272_);
v___x_3277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___x_3276_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; 
lean_dec(v_a_3272_);
v___x_3278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3278_;
}
}
else
{
lean_dec_ref_known(v___y_3256_, 2);
lean_dec_ref(v_post_3239_);
lean_dec_ref(v_pre_3237_);
return v___x_3271_;
}
}
case 11:
{
lean_object* v_typeName_3279_; lean_object* v_idx_3280_; lean_object* v_struct_3281_; lean_object* v___x_3282_; 
v_typeName_3279_ = lean_ctor_get(v___y_3256_, 0);
v_idx_3280_ = lean_ctor_get(v___y_3256_, 1);
v_struct_3281_ = lean_ctor_get(v___y_3256_, 2);
lean_inc_ref(v_struct_3281_);
lean_inc_ref(v_post_3239_);
lean_inc_ref(v_pre_3237_);
v___x_3282_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v_struct_3281_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; size_t v___x_3284_; size_t v___x_3285_; uint8_t v___x_3286_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3284_ = lean_ptr_addr(v_struct_3281_);
v___x_3285_ = lean_ptr_addr(v_a_3283_);
v___x_3286_ = lean_usize_dec_eq(v___x_3284_, v___x_3285_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_inc(v_idx_3280_);
lean_inc(v_typeName_3279_);
lean_dec_ref_known(v___y_3256_, 3);
v___x_3287_ = l_Lean_Expr_proj___override(v_typeName_3279_, v_idx_3280_, v_a_3283_);
v___x_3288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___x_3287_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; 
lean_dec(v_a_3283_);
v___x_3289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3289_;
}
}
else
{
lean_dec_ref_known(v___y_3256_, 3);
lean_dec_ref(v_post_3239_);
lean_dec_ref(v_pre_3237_);
return v___x_3282_;
}
}
default: 
{
lean_object* v___x_3290_; 
v___x_3290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3237_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___y_3256_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v_post_3239_);
lean_dec_ref(v_e_3238_);
lean_dec_ref(v_pre_3237_);
v_a_3300_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3250_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3250_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
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
lean_dec_ref(v_post_3239_);
lean_dec_ref(v_e_3238_);
lean_dec_ref(v_pre_3237_);
v_a_3308_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3249_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3249_);
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
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3236_ = stack[0].m_obj;
lean_object* v_pre_3237_ = stack[1].m_obj;
lean_object* v_e_3238_ = stack[2].m_obj;
lean_object* v_post_3239_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3240_ = stack[4].m_num;
uint8_t v_skipConstInApp_3241_ = stack[5].m_num;
uint8_t v_skipInstances_3242_ = stack[6].m_num;
lean_object* v___y_3243_ = stack[7].m_obj;
lean_object* v___y_3244_ = stack[8].m_obj;
lean_object* v___y_3245_ = stack[9].m_obj;
lean_object* v___y_3246_ = stack[10].m_obj;
lean_object* v___y_3247_ = stack[11].m_obj;
lean_object* v_res_3316_;
v_res_3316_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3236_, v_pre_3237_, v_e_3238_, v_post_3239_, v_usedLetOnly_3240_, v_skipConstInApp_3241_, v_skipInstances_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
stack->m_obj
 = v_res_3316_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3317_, lean_object* v_pre_3318_, lean_object* v_e_3319_, lean_object* v_post_3320_, lean_object* v_usedLetOnly_3321_, lean_object* v_skipConstInApp_3322_, lean_object* v_skipInstances_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_usedLetOnly_boxed_3330_; uint8_t v_skipConstInApp_boxed_3331_; uint8_t v_skipInstances_boxed_3332_; lean_object* v_res_3333_; 
v_usedLetOnly_boxed_3330_ = lean_unbox(v_usedLetOnly_3321_);
v_skipConstInApp_boxed_3331_ = lean_unbox(v_skipConstInApp_3322_);
v_skipInstances_boxed_3332_ = lean_unbox(v_skipInstances_3323_);
v_res_3333_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3317_, v_pre_3318_, v_e_3319_, v_post_3320_, v_usedLetOnly_boxed_3330_, v_skipConstInApp_boxed_3331_, v_skipInstances_boxed_3332_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
return v_res_3333_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3334_, lean_object* v_post_3335_, uint8_t v_usedLetOnly_3336_, uint8_t v_skipConstInApp_3337_, uint8_t v_skipInstances_3338_, lean_object* v_e_3339_, lean_object* v_a_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_inc(v_a_3340_);
v___x_3346_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3346_, 0, lean_box(0));
lean_closure_set(v___x_3346_, 1, lean_box(0));
lean_closure_set(v___x_3346_, 2, v_a_3340_);
v___x_3347_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3346_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3382_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3382_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3382_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3348_, v_e_3339_);
lean_dec(v_a_3348_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; 
lean_del_object(v___x_3350_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3354_ = lean_box(v_usedLetOnly_3336_);
v___x_3355_ = lean_box(v_skipConstInApp_3337_);
v___x_3356_ = lean_box(v_skipInstances_3338_);
lean_inc_ref(v_e_3339_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3357_, 0, v___x_3353_);
lean_closure_set(v___f_3357_, 1, v_pre_3334_);
lean_closure_set(v___f_3357_, 2, v_e_3339_);
lean_closure_set(v___f_3357_, 3, v_post_3335_);
lean_closure_set(v___f_3357_, 4, v___x_3354_);
lean_closure_set(v___f_3357_, 5, v___x_3355_);
lean_closure_set(v___f_3357_, 6, v___x_3356_);
v___x_3358_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3357_, v_a_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_n(v_a_3359_, 2);
lean_dec_ref_known(v___x_3358_, 1);
lean_inc(v_a_3340_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3360_, 0, v_a_3340_);
lean_closure_set(v___f_3360_, 1, v_e_3339_);
lean_closure_set(v___f_3360_, 2, v_a_3359_);
v___x_3361_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3360_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3361_, 0);
lean_dec(v_unused_3369_);
v___x_3363_ = v___x_3361_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v___x_3361_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v_a_3359_);
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3359_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec(v_a_3359_);
v_a_3370_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3361_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3361_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_dec_ref(v_e_3339_);
return v___x_3358_;
}
}
else
{
lean_object* v_val_3378_; lean_object* v___x_3380_; 
lean_dec_ref(v_e_3339_);
lean_dec_ref(v_post_3335_);
lean_dec_ref(v_pre_3334_);
v_val_3378_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v___x_3352_, 1);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_val_3378_);
v___x_3380_ = v___x_3350_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_val_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_e_3339_);
lean_dec_ref(v_post_3335_);
lean_dec_ref(v_pre_3334_);
v_a_3383_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3347_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3347_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3334_ = stack[0].m_obj;
lean_object* v_post_3335_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3336_ = stack[2].m_num;
uint8_t v_skipConstInApp_3337_ = stack[3].m_num;
uint8_t v_skipInstances_3338_ = stack[4].m_num;
lean_object* v_e_3339_ = stack[5].m_obj;
lean_object* v_a_3340_ = stack[6].m_obj;
lean_object* v___y_3341_ = stack[7].m_obj;
lean_object* v___y_3342_ = stack[8].m_obj;
lean_object* v___y_3343_ = stack[9].m_obj;
lean_object* v___y_3344_ = stack[10].m_obj;
lean_object* v_res_3391_;
v_res_3391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3334_, v_post_3335_, v_usedLetOnly_3336_, v_skipConstInApp_3337_, v_skipInstances_3338_, v_e_3339_, v_a_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
stack->m_obj
 = v_res_3391_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3392_, lean_object* v_post_3393_, uint8_t v_usedLetOnly_3394_, uint8_t v_skipConstInApp_3395_, uint8_t v_skipInstances_3396_, lean_object* v_fvars_3397_, lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
if (lean_obj_tag(v_e_3398_) == 7)
{
lean_object* v_binderName_3405_; lean_object* v_binderType_3406_; lean_object* v_body_3407_; uint8_t v_binderInfo_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___f_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_binderName_3405_ = lean_ctor_get(v_e_3398_, 0);
lean_inc(v_binderName_3405_);
v_binderType_3406_ = lean_ctor_get(v_e_3398_, 1);
lean_inc_ref(v_binderType_3406_);
v_body_3407_ = lean_ctor_get(v_e_3398_, 2);
lean_inc_ref(v_body_3407_);
v_binderInfo_3408_ = lean_ctor_get_uint8(v_e_3398_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3398_, 3);
v___x_3409_ = lean_box(v_usedLetOnly_3394_);
v___x_3410_ = lean_box(v_skipConstInApp_3395_);
v___x_3411_ = lean_box(v_skipInstances_3396_);
lean_inc_ref(v_post_3393_);
lean_inc_ref(v_pre_3392_);
lean_inc_ref(v_fvars_3397_);
v___f_3412_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3412_, 0, v_fvars_3397_);
lean_closure_set(v___f_3412_, 1, v_pre_3392_);
lean_closure_set(v___f_3412_, 2, v_post_3393_);
lean_closure_set(v___f_3412_, 3, v___x_3409_);
lean_closure_set(v___f_3412_, 4, v___x_3410_);
lean_closure_set(v___f_3412_, 5, v___x_3411_);
lean_closure_set(v___f_3412_, 6, v_body_3407_);
v___x_3413_ = lean_expr_instantiate_rev(v_binderType_3406_, v_fvars_3397_);
lean_dec_ref(v_fvars_3397_);
lean_dec_ref(v_binderType_3406_);
v___x_3414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3392_, v_post_3393_, v_usedLetOnly_3394_, v_skipConstInApp_3395_, v_skipInstances_3396_, v___x_3413_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v___x_3416_ = 0;
v___x_3417_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3405_, v_binderInfo_3408_, v_a_3415_, v___f_3412_, v___x_3416_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3417_;
}
else
{
lean_dec_ref(v___f_3412_);
lean_dec(v_binderName_3405_);
return v___x_3414_;
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_expr_instantiate_rev(v_e_3398_, v_fvars_3397_);
lean_dec_ref(v_e_3398_);
lean_inc_ref(v_post_3393_);
lean_inc_ref(v_pre_3392_);
v___x_3419_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3392_, v_post_3393_, v_usedLetOnly_3394_, v_skipConstInApp_3395_, v_skipInstances_3396_, v___x_3418_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; uint8_t v___x_3421_; uint8_t v___x_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3419_, 1);
v___x_3421_ = 0;
v___x_3422_ = 1;
v___x_3423_ = 1;
v___x_3424_ = l_Lean_Meta_mkForallFVars(v_fvars_3397_, v_a_3420_, v___x_3421_, v_usedLetOnly_3394_, v___x_3422_, v___x_3423_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec_ref(v_fvars_3397_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3392_, v_post_3393_, v_usedLetOnly_3394_, v_skipConstInApp_3395_, v_skipInstances_3396_, v_a_3425_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3426_;
}
else
{
lean_dec_ref(v_post_3393_);
lean_dec_ref(v_pre_3392_);
return v___x_3424_;
}
}
else
{
lean_dec_ref(v_fvars_3397_);
lean_dec_ref(v_post_3393_);
lean_dec_ref(v_pre_3392_);
return v___x_3419_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3392_ = stack[0].m_obj;
lean_object* v_post_3393_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3394_ = stack[2].m_num;
uint8_t v_skipConstInApp_3395_ = stack[3].m_num;
uint8_t v_skipInstances_3396_ = stack[4].m_num;
lean_object* v_fvars_3397_ = stack[5].m_obj;
lean_object* v_e_3398_ = stack[6].m_obj;
lean_object* v_a_3399_ = stack[7].m_obj;
lean_object* v___y_3400_ = stack[8].m_obj;
lean_object* v___y_3401_ = stack[9].m_obj;
lean_object* v___y_3402_ = stack[10].m_obj;
lean_object* v___y_3403_ = stack[11].m_obj;
lean_object* v_res_3427_;
v_res_3427_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3392_, v_post_3393_, v_usedLetOnly_3394_, v_skipConstInApp_3395_, v_skipInstances_3396_, v_fvars_3397_, v_e_3398_, v_a_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
stack->m_obj
 = v_res_3427_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3428_, lean_object* v_pre_3429_, lean_object* v_post_3430_, uint8_t v_usedLetOnly_3431_, uint8_t v_skipConstInApp_3432_, uint8_t v_skipInstances_3433_, lean_object* v_body_3434_, lean_object* v_x_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_array_push(v_fvars_3428_, v_x_3435_);
v___x_3443_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3429_, v_post_3430_, v_usedLetOnly_3431_, v_skipConstInApp_3432_, v_skipInstances_3433_, v___x_3442_, v_body_3434_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3428_ = stack[0].m_obj;
lean_object* v_pre_3429_ = stack[1].m_obj;
lean_object* v_post_3430_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3431_ = stack[3].m_num;
uint8_t v_skipConstInApp_3432_ = stack[4].m_num;
uint8_t v_skipInstances_3433_ = stack[5].m_num;
lean_object* v_body_3434_ = stack[6].m_obj;
lean_object* v_x_3435_ = stack[7].m_obj;
lean_object* v___y_3436_ = stack[8].m_obj;
lean_object* v___y_3437_ = stack[9].m_obj;
lean_object* v___y_3438_ = stack[10].m_obj;
lean_object* v___y_3439_ = stack[11].m_obj;
lean_object* v___y_3440_ = stack[12].m_obj;
lean_object* v_res_3444_;
v_res_3444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3428_, v_pre_3429_, v_post_3430_, v_usedLetOnly_3431_, v_skipConstInApp_3432_, v_skipInstances_3433_, v_body_3434_, v_x_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
stack->m_obj
 = v_res_3444_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3445_, lean_object* v_post_3446_, lean_object* v_usedLetOnly_3447_, lean_object* v_skipConstInApp_3448_, lean_object* v_skipInstances_3449_, lean_object* v_e_3450_, lean_object* v_a_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
uint8_t v_usedLetOnly_boxed_3457_; uint8_t v_skipConstInApp_boxed_3458_; uint8_t v_skipInstances_boxed_3459_; lean_object* v_res_3460_; 
v_usedLetOnly_boxed_3457_ = lean_unbox(v_usedLetOnly_3447_);
v_skipConstInApp_boxed_3458_ = lean_unbox(v_skipConstInApp_3448_);
v_skipInstances_boxed_3459_ = lean_unbox(v_skipInstances_3449_);
v_res_3460_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3445_, v_post_3446_, v_usedLetOnly_boxed_3457_, v_skipConstInApp_boxed_3458_, v_skipInstances_boxed_3459_, v_e_3450_, v_a_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v_a_3451_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3461_, lean_object* v_post_3462_, lean_object* v_usedLetOnly_3463_, lean_object* v_skipConstInApp_3464_, lean_object* v_skipInstances_3465_, lean_object* v_sz_3466_, lean_object* v_i_3467_, lean_object* v_bs_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v_usedLetOnly_boxed_3475_; uint8_t v_skipConstInApp_boxed_3476_; uint8_t v_skipInstances_boxed_3477_; size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_usedLetOnly_boxed_3475_ = lean_unbox(v_usedLetOnly_3463_);
v_skipConstInApp_boxed_3476_ = lean_unbox(v_skipConstInApp_3464_);
v_skipInstances_boxed_3477_ = lean_unbox(v_skipInstances_3465_);
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3466_);
lean_dec(v_sz_3466_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3467_);
lean_dec(v_i_3467_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3461_, v_post_3462_, v_usedLetOnly_boxed_3475_, v_skipConstInApp_boxed_3476_, v_skipInstances_boxed_3477_, v_sz_boxed_3478_, v_i_boxed_3479_, v_bs_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3481_, lean_object* v_post_3482_, lean_object* v_usedLetOnly_3483_, lean_object* v_skipConstInApp_3484_, lean_object* v_skipInstances_3485_, lean_object* v_e_3486_, lean_object* v_a_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v_usedLetOnly_boxed_3493_; uint8_t v_skipConstInApp_boxed_3494_; uint8_t v_skipInstances_boxed_3495_; lean_object* v_res_3496_; 
v_usedLetOnly_boxed_3493_ = lean_unbox(v_usedLetOnly_3483_);
v_skipConstInApp_boxed_3494_ = lean_unbox(v_skipConstInApp_3484_);
v_skipInstances_boxed_3495_ = lean_unbox(v_skipInstances_3485_);
v_res_3496_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3481_, v_post_3482_, v_usedLetOnly_boxed_3493_, v_skipConstInApp_boxed_3494_, v_skipInstances_boxed_3495_, v_e_3486_, v_a_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v_a_3487_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3497_, lean_object* v_post_3498_, lean_object* v_usedLetOnly_3499_, lean_object* v_skipConstInApp_3500_, lean_object* v_skipInstances_3501_, lean_object* v_fvars_3502_, lean_object* v_e_3503_, lean_object* v_a_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
uint8_t v_usedLetOnly_boxed_3510_; uint8_t v_skipConstInApp_boxed_3511_; uint8_t v_skipInstances_boxed_3512_; lean_object* v_res_3513_; 
v_usedLetOnly_boxed_3510_ = lean_unbox(v_usedLetOnly_3499_);
v_skipConstInApp_boxed_3511_ = lean_unbox(v_skipConstInApp_3500_);
v_skipInstances_boxed_3512_ = lean_unbox(v_skipInstances_3501_);
v_res_3513_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3497_, v_post_3498_, v_usedLetOnly_boxed_3510_, v_skipConstInApp_boxed_3511_, v_skipInstances_boxed_3512_, v_fvars_3502_, v_e_3503_, v_a_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v_a_3504_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3514_, lean_object* v_post_3515_, lean_object* v_usedLetOnly_3516_, lean_object* v_skipConstInApp_3517_, lean_object* v_skipInstances_3518_, lean_object* v_fvars_3519_, lean_object* v_e_3520_, lean_object* v_a_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v_usedLetOnly_boxed_3527_; uint8_t v_skipConstInApp_boxed_3528_; uint8_t v_skipInstances_boxed_3529_; lean_object* v_res_3530_; 
v_usedLetOnly_boxed_3527_ = lean_unbox(v_usedLetOnly_3516_);
v_skipConstInApp_boxed_3528_ = lean_unbox(v_skipConstInApp_3517_);
v_skipInstances_boxed_3529_ = lean_unbox(v_skipInstances_3518_);
v_res_3530_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3514_, v_post_3515_, v_usedLetOnly_boxed_3527_, v_skipConstInApp_boxed_3528_, v_skipInstances_boxed_3529_, v_fvars_3519_, v_e_3520_, v_a_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v_a_3521_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3531_, lean_object* v_post_3532_, lean_object* v_usedLetOnly_3533_, lean_object* v_skipConstInApp_3534_, lean_object* v_skipInstances_3535_, lean_object* v_fvars_3536_, lean_object* v_e_3537_, lean_object* v_a_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
uint8_t v_usedLetOnly_boxed_3544_; uint8_t v_skipConstInApp_boxed_3545_; uint8_t v_skipInstances_boxed_3546_; lean_object* v_res_3547_; 
v_usedLetOnly_boxed_3544_ = lean_unbox(v_usedLetOnly_3533_);
v_skipConstInApp_boxed_3545_ = lean_unbox(v_skipConstInApp_3534_);
v_skipInstances_boxed_3546_ = lean_unbox(v_skipInstances_3535_);
v_res_3547_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3531_, v_post_3532_, v_usedLetOnly_boxed_3544_, v_skipConstInApp_boxed_3545_, v_skipInstances_boxed_3546_, v_fvars_3536_, v_e_3537_, v_a_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v_a_3538_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3548_, lean_object* v___x_3549_, lean_object* v_pre_3550_, lean_object* v_post_3551_, lean_object* v_usedLetOnly_3552_, lean_object* v_skipConstInApp_3553_, lean_object* v_skipInstances_3554_, lean_object* v_a_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_usedLetOnly_boxed_3563_; uint8_t v_skipConstInApp_boxed_3564_; uint8_t v_skipInstances_boxed_3565_; lean_object* v_res_3566_; 
v_usedLetOnly_boxed_3563_ = lean_unbox(v_usedLetOnly_3552_);
v_skipConstInApp_boxed_3564_ = lean_unbox(v_skipConstInApp_3553_);
v_skipInstances_boxed_3565_ = lean_unbox(v_skipInstances_3554_);
v_res_3566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3548_, v___x_3549_, v_pre_3550_, v_post_3551_, v_usedLetOnly_boxed_3563_, v_skipConstInApp_boxed_3564_, v_skipInstances_boxed_3565_, v_a_3555_, v_b_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___x_3549_);
lean_dec(v_upperBound_3548_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3567_, lean_object* v_pre_3568_, lean_object* v_post_3569_, lean_object* v_usedLetOnly_3570_, lean_object* v_skipConstInApp_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v_skipInstances_boxed_3581_; uint8_t v_usedLetOnly_boxed_3582_; uint8_t v_skipConstInApp_boxed_3583_; lean_object* v_res_3584_; 
v_skipInstances_boxed_3581_ = lean_unbox(v_skipInstances_3567_);
v_usedLetOnly_boxed_3582_ = lean_unbox(v_usedLetOnly_3570_);
v_skipConstInApp_boxed_3583_ = lean_unbox(v_skipConstInApp_3571_);
v_res_3584_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3581_, v_pre_3568_, v_post_3569_, v_usedLetOnly_boxed_3582_, v_skipConstInApp_boxed_3583_, v_x_3572_, v_x_3573_, v_x_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
return v_res_3584_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_box(0);
v___x_3586_ = lean_unsigned_to_nat(16u);
v___x_3587_ = lean_mk_array(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___x_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3592_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3592_, 0, lean_box(0));
lean_closure_set(v___x_3592_, 1, lean_box(0));
lean_closure_set(v___x_3592_, 2, v___x_3591_);
return v___x_3592_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3593_, lean_object* v_pre_3594_, lean_object* v_post_3595_, uint8_t v_usedLetOnly_3596_, uint8_t v_skipConstInApp_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_a_3606_; lean_object* v___x_3607_; 
v___x_3603_ = 0;
v___x_3604_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3605_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3604_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3594_, v_post_3595_, v_usedLetOnly_3596_, v_skipConstInApp_3597_, v___x_3603_, v_input_3593_, v_a_3606_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3609_, 0, lean_box(0));
lean_closure_set(v___x_3609_, 1, lean_box(0));
lean_closure_set(v___x_3609_, 2, v_a_3606_);
v___x_3610_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3609_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v___x_3610_, 0);
lean_dec(v_unused_3618_);
v___x_3612_ = v___x_3610_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_dec(v___x_3610_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v_a_3608_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3608_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
else
{
lean_dec(v_a_3606_);
return v___x_3607_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3593_ = stack[0].m_obj;
lean_object* v_pre_3594_ = stack[1].m_obj;
lean_object* v_post_3595_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3596_ = stack[3].m_num;
uint8_t v_skipConstInApp_3597_ = stack[4].m_num;
lean_object* v___y_3598_ = stack[5].m_obj;
lean_object* v___y_3599_ = stack[6].m_obj;
lean_object* v___y_3600_ = stack[7].m_obj;
lean_object* v___y_3601_ = stack[8].m_obj;
lean_object* v_res_3619_;
v_res_3619_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3593_, v_pre_3594_, v_post_3595_, v_usedLetOnly_3596_, v_skipConstInApp_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
stack->m_obj
 = v_res_3619_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3620_, lean_object* v_pre_3621_, lean_object* v_post_3622_, lean_object* v_usedLetOnly_3623_, lean_object* v_skipConstInApp_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v_usedLetOnly_boxed_3630_; uint8_t v_skipConstInApp_boxed_3631_; lean_object* v_res_3632_; 
v_usedLetOnly_boxed_3630_ = lean_unbox(v_usedLetOnly_3623_);
v_skipConstInApp_boxed_3631_ = lean_unbox(v_skipConstInApp_3624_);
v_res_3632_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3620_, v_pre_3621_, v_post_3622_, v_usedLetOnly_boxed_3630_, v_skipConstInApp_boxed_3631_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3632_;
}
}
lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3634_, lean_object* v_p_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v___f_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v_a_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; 
v___f_3641_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3642_, 0, v_p_3635_);
v___x_3643_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3634_, v_a_3637_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = 0;
v___x_3646_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3644_, v___f_3641_, v___f_3642_, v___x_3645_, v___x_3645_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
return v___x_3646_;
}
}
LEAN_EXPORT void l_Lean_Meta_etaStructReduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3634_ = stack[0].m_obj;
lean_object* v_p_3635_ = stack[1].m_obj;
lean_object* v_a_3636_ = stack[2].m_obj;
lean_object* v_a_3637_ = stack[3].m_obj;
lean_object* v_a_3638_ = stack[4].m_obj;
lean_object* v_a_3639_ = stack[5].m_obj;
lean_object* v_res_3647_;
v_res_3647_ = l_Lean_Meta_etaStructReduce(v_e_3634_, v_p_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
stack->m_obj
 = v_res_3647_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3648_, lean_object* v_p_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_Meta_etaStructReduce(v_e_3648_, v_p_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
return v_res_3655_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3656_, lean_object* v___x_3657_, lean_object* v_pre_3658_, lean_object* v_post_3659_, uint8_t v_usedLetOnly_3660_, uint8_t v_skipConstInApp_3661_, uint8_t v_skipInstances_3662_, lean_object* v___x_3663_, lean_object* v_inst_3664_, lean_object* v_R_3665_, lean_object* v_a_3666_, lean_object* v_b_3667_, lean_object* v_c_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3656_, v___x_3657_, v_pre_3658_, v_post_3659_, v_usedLetOnly_3660_, v_skipConstInApp_3661_, v_skipInstances_3662_, v_a_3666_, v_b_3667_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3656_ = stack[0].m_obj;
lean_object* v___x_3657_ = stack[1].m_obj;
lean_object* v_pre_3658_ = stack[2].m_obj;
lean_object* v_post_3659_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3660_ = stack[4].m_num;
uint8_t v_skipConstInApp_3661_ = stack[5].m_num;
uint8_t v_skipInstances_3662_ = stack[6].m_num;
lean_object* v___x_3663_ = stack[7].m_obj;
lean_object* v_a_3666_ = stack[10].m_obj;
lean_object* v_b_3667_ = stack[11].m_obj;
lean_object* v___y_3669_ = stack[13].m_obj;
lean_object* v___y_3670_ = stack[14].m_obj;
lean_object* v___y_3671_ = stack[15].m_obj;
lean_object* v___y_3672_ = stack[16].m_obj;
lean_object* v___y_3673_ = stack[17].m_obj;
lean_object* v_res_3676_;
v_res_3676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3656_, v___x_3657_, v_pre_3658_, v_post_3659_, v_usedLetOnly_3660_, v_skipConstInApp_3661_, v_skipInstances_3662_, v___x_3663_, lean_box(0), lean_box(0), v_a_3666_, v_b_3667_, lean_box(0), v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
stack->m_obj
 = v_res_3676_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3677_ = _args[0];
lean_object* v___x_3678_ = _args[1];
lean_object* v_pre_3679_ = _args[2];
lean_object* v_post_3680_ = _args[3];
lean_object* v_usedLetOnly_3681_ = _args[4];
lean_object* v_skipConstInApp_3682_ = _args[5];
lean_object* v_skipInstances_3683_ = _args[6];
lean_object* v___x_3684_ = _args[7];
lean_object* v_inst_3685_ = _args[8];
lean_object* v_R_3686_ = _args[9];
lean_object* v_a_3687_ = _args[10];
lean_object* v_b_3688_ = _args[11];
lean_object* v_c_3689_ = _args[12];
lean_object* v___y_3690_ = _args[13];
lean_object* v___y_3691_ = _args[14];
lean_object* v___y_3692_ = _args[15];
lean_object* v___y_3693_ = _args[16];
lean_object* v___y_3694_ = _args[17];
lean_object* v___y_3695_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3696_; uint8_t v_skipConstInApp_boxed_3697_; uint8_t v_skipInstances_boxed_3698_; lean_object* v_res_3699_; 
v_usedLetOnly_boxed_3696_ = lean_unbox(v_usedLetOnly_3681_);
v_skipConstInApp_boxed_3697_ = lean_unbox(v_skipConstInApp_3682_);
v_skipInstances_boxed_3698_ = lean_unbox(v_skipInstances_3683_);
v_res_3699_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3677_, v___x_3678_, v_pre_3679_, v_post_3680_, v_usedLetOnly_boxed_3696_, v_skipConstInApp_boxed_3697_, v_skipInstances_boxed_3698_, v___x_3684_, v_inst_3685_, v_R_3686_, v_a_3687_, v_b_3688_, v_c_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec(v___x_3684_);
lean_dec_ref(v___x_3678_);
lean_dec(v_upperBound_3677_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3700_, lean_object* v_m_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3701_, v_a_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3704_, lean_object* v_m_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3704_, v_m_3705_, v_a_3706_);
lean_dec_ref(v_a_3706_);
lean_dec_ref(v_m_3705_);
return v_res_3707_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3708_, lean_object* v_name_3709_, uint8_t v_bi_3710_, lean_object* v_type_3711_, lean_object* v_k_3712_, uint8_t v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3709_, v_bi_3710_, v_type_3711_, v_k_3712_, v_kind_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3720_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3709_ = stack[1].m_obj;
uint8_t v_bi_3710_ = stack[2].m_num;
lean_object* v_type_3711_ = stack[3].m_obj;
lean_object* v_k_3712_ = stack[4].m_obj;
uint8_t v_kind_3713_ = stack[5].m_num;
lean_object* v___y_3714_ = stack[6].m_obj;
lean_object* v___y_3715_ = stack[7].m_obj;
lean_object* v___y_3716_ = stack[8].m_obj;
lean_object* v___y_3717_ = stack[9].m_obj;
lean_object* v___y_3718_ = stack[10].m_obj;
lean_object* v_res_3721_;
v_res_3721_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_box(0), v_name_3709_, v_bi_3710_, v_type_3711_, v_k_3712_, v_kind_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
stack->m_obj
 = v_res_3721_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3722_, lean_object* v_name_3723_, lean_object* v_bi_3724_, lean_object* v_type_3725_, lean_object* v_k_3726_, lean_object* v_kind_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_bi_boxed_3734_; uint8_t v_kind_boxed_3735_; lean_object* v_res_3736_; 
v_bi_boxed_3734_ = lean_unbox(v_bi_3724_);
v_kind_boxed_3735_ = lean_unbox(v_kind_3727_);
v_res_3736_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3722_, v_name_3723_, v_bi_boxed_3734_, v_type_3725_, v_k_3726_, v_kind_boxed_3735_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
return v_res_3736_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3737_, lean_object* v_name_3738_, lean_object* v_type_3739_, lean_object* v_val_3740_, lean_object* v_k_3741_, uint8_t v_nondep_3742_, uint8_t v_kind_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3738_, v_type_3739_, v_val_3740_, v_k_3741_, v_nondep_3742_, v_kind_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3738_ = stack[1].m_obj;
lean_object* v_type_3739_ = stack[2].m_obj;
lean_object* v_val_3740_ = stack[3].m_obj;
lean_object* v_k_3741_ = stack[4].m_obj;
uint8_t v_nondep_3742_ = stack[5].m_num;
uint8_t v_kind_3743_ = stack[6].m_num;
lean_object* v___y_3744_ = stack[7].m_obj;
lean_object* v___y_3745_ = stack[8].m_obj;
lean_object* v___y_3746_ = stack[9].m_obj;
lean_object* v___y_3747_ = stack[10].m_obj;
lean_object* v___y_3748_ = stack[11].m_obj;
lean_object* v_res_3751_;
v_res_3751_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_box(0), v_name_3738_, v_type_3739_, v_val_3740_, v_k_3741_, v_nondep_3742_, v_kind_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
stack->m_obj
 = v_res_3751_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3752_, lean_object* v_name_3753_, lean_object* v_type_3754_, lean_object* v_val_3755_, lean_object* v_k_3756_, lean_object* v_nondep_3757_, lean_object* v_kind_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_nondep_boxed_3765_; uint8_t v_kind_boxed_3766_; lean_object* v_res_3767_; 
v_nondep_boxed_3765_ = lean_unbox(v_nondep_3757_);
v_kind_boxed_3766_ = lean_unbox(v_kind_3758_);
v_res_3767_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3752_, v_name_3753_, v_type_3754_, v_val_3755_, v_k_3756_, v_nondep_boxed_3765_, v_kind_boxed_3766_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
return v_res_3767_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3768_, lean_object* v_ref_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3769_);
return v___x_3775_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3769_ = stack[1].m_obj;
lean_object* v___y_3770_ = stack[2].m_obj;
lean_object* v___y_3771_ = stack[3].m_obj;
lean_object* v___y_3772_ = stack[4].m_obj;
lean_object* v___y_3773_ = stack[5].m_obj;
lean_object* v_res_3776_;
v_res_3776_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_box(0), v_ref_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
stack->m_obj
 = v_res_3776_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3777_, lean_object* v_ref_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3777_, v_ref_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3784_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3785_, lean_object* v_x_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3786_ = stack[1].m_obj;
lean_object* v___y_3787_ = stack[2].m_obj;
lean_object* v___y_3788_ = stack[3].m_obj;
lean_object* v___y_3789_ = stack[4].m_obj;
lean_object* v___y_3790_ = stack[5].m_obj;
lean_object* v___y_3791_ = stack[6].m_obj;
lean_object* v_res_3794_;
v_res_3794_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_box(0), v_x_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
stack->m_obj
 = v_res_3794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3795_, v_x_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3804_, lean_object* v_m_3805_, lean_object* v_a_3806_, lean_object* v_b_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3805_, v_a_3806_, v_b_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3809_, lean_object* v_a_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3810_, v_x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3813_, lean_object* v_a_3814_, lean_object* v_x_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3813_, v_a_3814_, v_x_3815_);
lean_dec(v_x_3815_);
lean_dec_ref(v_a_3814_);
return v_res_3816_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3817_, lean_object* v_a_3818_, lean_object* v_x_3819_){
_start:
{
uint8_t v___x_3820_; 
v___x_3820_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3818_, v_x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3818_ = stack[1].m_obj;
lean_object* v_x_3819_ = stack[2].m_obj;
uint8_t v_res_3821_;
v_res_3821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_box(0), v_a_3818_, v_x_3819_);
stack->m_num = v_res_3821_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3822_, lean_object* v_a_3823_, lean_object* v_x_3824_){
_start:
{
uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_res_3825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3822_, v_a_3823_, v_x_3824_);
lean_dec(v_x_3824_);
lean_dec_ref(v_a_3823_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3827_, lean_object* v_data_3828_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_, lean_object* v_x_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3831_, v_b_3832_, v_x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3835_, lean_object* v_i_3836_, lean_object* v_source_3837_, lean_object* v_target_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3836_, v_source_3837_, v_target_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3840_, lean_object* v_x_3841_, lean_object* v_x_3842_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3841_, v_x_3842_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3844_, lean_object* v_inst_3845_, lean_object* v_toBind_3846_, lean_object* v___f_3847_, lean_object* v_____do__lift_3848_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3849_, 0, v_____do__lift_3848_);
lean_closure_set(v___x_3849_, 1, v_binderType_3844_);
v___x_3850_ = lean_apply_2(v_inst_3845_, lean_box(0), v___x_3849_);
v___x_3851_ = lean_apply_4(v_toBind_3846_, lean_box(0), lean_box(0), v___x_3850_, v___f_3847_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3852_, lean_object* v_usedFields_3853_, lean_object* v_binderName_3854_, lean_object* v_body_3855_, lean_object* v_val_3856_, lean_object* v_inst_3857_, lean_object* v_inst_3858_, lean_object* v_fieldVal_x3f_3859_, lean_object* v_____do__lift_3860_){
_start:
{
uint8_t v_____do__lift_298__boxed_3861_; lean_object* v_res_3862_; 
v_____do__lift_298__boxed_3861_ = lean_unbox(v_____do__lift_3860_);
v_res_3862_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3852_, v_usedFields_3853_, v_binderName_3854_, v_body_3855_, v_val_3856_, v_inst_3857_, v_inst_3858_, v_fieldVal_x3f_3859_, v_____do__lift_298__boxed_3861_);
lean_dec_ref(v_val_3856_);
lean_dec_ref(v_body_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3863_, lean_object* v_usedFields_3864_, lean_object* v_binderName_3865_, lean_object* v_body_3866_, lean_object* v_inst_3867_, lean_object* v_inst_3868_, lean_object* v_fieldVal_x3f_3869_, lean_object* v_binderType_3870_, lean_object* v_toBind_3871_, lean_object* v_____x_3872_){
_start:
{
if (lean_obj_tag(v_____x_3872_) == 1)
{
lean_object* v_val_3873_; lean_object* v___f_3874_; lean_object* v___f_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_val_3873_ = lean_ctor_get(v_____x_3872_, 0);
lean_inc_n(v_val_3873_, 2);
lean_dec_ref_known(v_____x_3872_, 1);
lean_inc_n(v_inst_3868_, 2);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3874_, 0, v_toPure_3863_);
lean_closure_set(v___f_3874_, 1, v_usedFields_3864_);
lean_closure_set(v___f_3874_, 2, v_binderName_3865_);
lean_closure_set(v___f_3874_, 3, v_body_3866_);
lean_closure_set(v___f_3874_, 4, v_val_3873_);
lean_closure_set(v___f_3874_, 5, v_inst_3867_);
lean_closure_set(v___f_3874_, 6, v_inst_3868_);
lean_closure_set(v___f_3874_, 7, v_fieldVal_x3f_3869_);
lean_inc(v_toBind_3871_);
v___f_3875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3875_, 0, v_binderType_3870_);
lean_closure_set(v___f_3875_, 1, v_inst_3868_);
lean_closure_set(v___f_3875_, 2, v_toBind_3871_);
lean_closure_set(v___f_3875_, 3, v___f_3874_);
v___x_3876_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3876_, 0, v_val_3873_);
v___x_3877_ = lean_apply_2(v_inst_3868_, lean_box(0), v___x_3876_);
v___x_3878_ = lean_apply_4(v_toBind_3871_, lean_box(0), lean_box(0), v___x_3877_, v___f_3875_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
lean_dec(v_____x_3872_);
lean_dec(v_toBind_3871_);
lean_dec_ref(v_binderType_3870_);
lean_dec(v_fieldVal_x3f_3869_);
lean_dec(v_inst_3868_);
lean_dec_ref(v_inst_3867_);
lean_dec_ref(v_body_3866_);
lean_dec(v_binderName_3865_);
lean_dec(v_usedFields_3864_);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_apply_2(v_toPure_3863_, lean_box(0), v___x_3879_);
return v___x_3880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3884_, lean_object* v_inst_3885_, lean_object* v_fieldVal_x3f_3886_, lean_object* v_usedFields_3887_, lean_object* v_e_3888_){
_start:
{
lean_object* v_toApplicative_3889_; lean_object* v_toBind_3890_; lean_object* v_toPure_3891_; 
v_toApplicative_3889_ = lean_ctor_get(v_inst_3884_, 0);
v_toBind_3890_ = lean_ctor_get(v_inst_3884_, 1);
v_toPure_3891_ = lean_ctor_get(v_toApplicative_3889_, 1);
lean_inc(v_toPure_3891_);
if (lean_obj_tag(v_e_3888_) == 6)
{
lean_object* v_binderName_3896_; lean_object* v_binderType_3897_; lean_object* v_body_3898_; lean_object* v___f_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_inc_n(v_toBind_3890_, 2);
v_binderName_3896_ = lean_ctor_get(v_e_3888_, 0);
lean_inc_n(v_binderName_3896_, 2);
v_binderType_3897_ = lean_ctor_get(v_e_3888_, 1);
lean_inc_ref(v_binderType_3897_);
v_body_3898_ = lean_ctor_get(v_e_3888_, 2);
lean_inc_ref(v_body_3898_);
lean_dec_ref_known(v_e_3888_, 3);
lean_inc(v_fieldVal_x3f_3886_);
v___f_3899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3899_, 0, v_toPure_3891_);
lean_closure_set(v___f_3899_, 1, v_usedFields_3887_);
lean_closure_set(v___f_3899_, 2, v_binderName_3896_);
lean_closure_set(v___f_3899_, 3, v_body_3898_);
lean_closure_set(v___f_3899_, 4, v_inst_3884_);
lean_closure_set(v___f_3899_, 5, v_inst_3885_);
lean_closure_set(v___f_3899_, 6, v_fieldVal_x3f_3886_);
lean_closure_set(v___f_3899_, 7, v_binderType_3897_);
lean_closure_set(v___f_3899_, 8, v_toBind_3890_);
v___x_3900_ = lean_apply_1(v_fieldVal_x3f_3886_, v_binderName_3896_);
v___x_3901_ = lean_apply_4(v_toBind_3890_, lean_box(0), lean_box(0), v___x_3900_, v___f_3899_);
return v___x_3901_;
}
else
{
lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v_fieldVal_x3f_3886_);
lean_dec(v_inst_3885_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_inst_3884_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; lean_object* v_unused_3920_; 
v_unused_3919_ = lean_ctor_get(v_inst_3884_, 1);
lean_dec(v_unused_3919_);
v_unused_3920_ = lean_ctor_get(v_inst_3884_, 0);
lean_dec(v_unused_3920_);
v___x_3903_ = v_inst_3884_;
v_isShared_3904_ = v_isSharedCheck_3918_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v_inst_3884_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3918_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; uint8_t v___x_3906_; 
lean_inc_ref(v_e_3888_);
v___x_3905_ = l_Lean_Expr_cleanupAnnotations(v_e_3888_);
v___x_3906_ = l_Lean_Expr_isApp(v___x_3905_);
if (v___x_3906_ == 0)
{
lean_dec_ref(v___x_3905_);
lean_del_object(v___x_3903_);
goto v___jp_3892_;
}
else
{
lean_object* v_arg_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_arg_3907_ = lean_ctor_get(v___x_3905_, 1);
lean_inc_ref(v_arg_3907_);
v___x_3908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3905_);
v___x_3909_ = l_Lean_Expr_isApp(v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec_ref(v___x_3908_);
lean_dec_ref(v_arg_3907_);
lean_del_object(v___x_3903_);
goto v___jp_3892_;
}
else
{
lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3910_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3908_);
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3912_ = l_Lean_Expr_isConstOf(v___x_3910_, v___x_3911_);
lean_dec_ref(v___x_3910_);
if (v___x_3912_ == 0)
{
lean_dec_ref(v_arg_3907_);
lean_del_object(v___x_3903_);
goto v___jp_3892_;
}
else
{
lean_object* v___x_3914_; 
lean_dec_ref(v_e_3888_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 1, v_arg_3907_);
lean_ctor_set(v___x_3903_, 0, v_usedFields_3887_);
v___x_3914_ = v___x_3903_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_usedFields_3887_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_arg_3907_);
v___x_3914_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
v___x_3916_ = lean_apply_2(v_toPure_3891_, lean_box(0), v___x_3915_);
return v___x_3916_;
}
}
}
}
}
}
v___jp_3892_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_usedFields_3887_);
lean_ctor_set(v___x_3893_, 1, v_e_3888_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v___x_3895_ = lean_apply_2(v_toPure_3891_, lean_box(0), v___x_3894_);
return v___x_3895_;
}
}
}
lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3921_, lean_object* v_usedFields_3922_, lean_object* v_binderName_3923_, lean_object* v_body_3924_, lean_object* v_val_3925_, lean_object* v_inst_3926_, lean_object* v_inst_3927_, lean_object* v_fieldVal_x3f_3928_, uint8_t v_____do__lift_3929_){
_start:
{
if (v_____do__lift_3929_ == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_dec(v_fieldVal_x3f_3928_);
lean_dec(v_inst_3927_);
lean_dec_ref(v_inst_3926_);
lean_dec(v_binderName_3923_);
lean_dec(v_usedFields_3922_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_apply_2(v_toPure_3921_, lean_box(0), v___x_3930_);
return v___x_3931_;
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec(v_toPure_3921_);
v___x_3932_ = l_Lean_NameSet_insert(v_usedFields_3922_, v_binderName_3923_);
v___x_3933_ = lean_expr_instantiate1(v_body_3924_, v_val_3925_);
v___x_3934_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3926_, v_inst_3927_, v_fieldVal_x3f_3928_, v___x_3932_, v___x_3933_);
return v___x_3934_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3921_ = stack[0].m_obj;
lean_object* v_usedFields_3922_ = stack[1].m_obj;
lean_object* v_binderName_3923_ = stack[2].m_obj;
lean_object* v_body_3924_ = stack[3].m_obj;
lean_object* v_val_3925_ = stack[4].m_obj;
lean_object* v_inst_3926_ = stack[5].m_obj;
lean_object* v_inst_3927_ = stack[6].m_obj;
lean_object* v_fieldVal_x3f_3928_ = stack[7].m_obj;
uint8_t v_____do__lift_3929_ = stack[8].m_num;
lean_object* v_res_3935_;
v_res_3935_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3921_, v_usedFields_3922_, v_binderName_3923_, v_body_3924_, v_val_3925_, v_inst_3926_, v_inst_3927_, v_fieldVal_x3f_3928_, v_____do__lift_3929_);
stack->m_obj
 = v_res_3935_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3936_, lean_object* v_inst_3937_, lean_object* v_inst_3938_, lean_object* v_fieldVal_x3f_3939_, lean_object* v_usedFields_3940_, lean_object* v_e_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3937_, v_inst_3938_, v_fieldVal_x3f_3939_, v_usedFields_3940_, v_e_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3943_, lean_object* v_inst_3944_, lean_object* v_fieldVal_x3f_3945_, lean_object* v_toPure_3946_, lean_object* v_____s_3947_){
_start:
{
lean_object* v_fst_3948_; 
v_fst_3948_ = lean_ctor_get(v_____s_3947_, 0);
if (lean_obj_tag(v_fst_3948_) == 0)
{
lean_object* v_snd_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec(v_toPure_3946_);
v_snd_3949_ = lean_ctor_get(v_____s_3947_, 1);
lean_inc(v_snd_3949_);
lean_dec_ref(v_____s_3947_);
v___x_3950_ = l_Lean_NameSet_empty;
v___x_3951_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3943_, v_inst_3944_, v_fieldVal_x3f_3945_, v___x_3950_, v_snd_3949_);
return v___x_3951_;
}
else
{
lean_object* v_val_3952_; lean_object* v___x_3953_; 
lean_inc_ref(v_fst_3948_);
lean_dec_ref(v_____s_3947_);
lean_dec(v_fieldVal_x3f_3945_);
lean_dec(v_inst_3944_);
lean_dec_ref(v_inst_3943_);
v_val_3952_ = lean_ctor_get(v_fst_3948_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v_fst_3948_, 1);
v___x_3953_ = lean_apply_2(v_toPure_3946_, lean_box(0), v_val_3952_);
return v___x_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3954_, lean_object* v_a_3955_, lean_object* v___x_3956_, lean_object* v_toPure_3957_, lean_object* v_____r_3958_){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3959_ = lean_expr_instantiate1(v_body_3954_, v_a_3955_);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3956_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v___x_3962_ = lean_apply_2(v_toPure_3957_, lean_box(0), v___x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3963_, lean_object* v_a_3964_, lean_object* v___x_3965_, lean_object* v_toPure_3966_, lean_object* v_____r_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3963_, v_a_3964_, v___x_3965_, v_toPure_3966_, v_____r_3967_);
lean_dec_ref(v_a_3964_);
lean_dec_ref(v_body_3963_);
return v_res_3968_;
}
}
lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3971_, lean_object* v_toPure_3972_, lean_object* v___f_3973_, uint8_t v_____do__lift_3974_){
_start:
{
if (v_____do__lift_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
lean_dec(v___f_3973_);
v___x_3975_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v_snd_3971_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = lean_apply_2(v_toPure_3972_, lean_box(0), v___x_3977_);
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_toPure_3972_);
lean_dec(v_snd_3971_);
v___x_3979_ = lean_box(0);
v___x_3980_ = lean_apply_1(v___f_3973_, v___x_3979_);
return v___x_3980_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3971_ = stack[0].m_obj;
lean_object* v_toPure_3972_ = stack[1].m_obj;
lean_object* v___f_3973_ = stack[2].m_obj;
uint8_t v_____do__lift_3974_ = stack[3].m_num;
lean_object* v_res_3981_;
v_res_3981_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3971_, v_toPure_3972_, v___f_3973_, v_____do__lift_3974_);
stack->m_obj
 = v_res_3981_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3982_, lean_object* v_toPure_3983_, lean_object* v___f_3984_, lean_object* v_____do__lift_3985_){
_start:
{
uint8_t v_____do__lift_583__boxed_3986_; lean_object* v_res_3987_; 
v_____do__lift_583__boxed_3986_ = lean_unbox(v_____do__lift_3985_);
v_res_3987_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3982_, v_toPure_3983_, v___f_3984_, v_____do__lift_583__boxed_3986_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3988_, lean_object* v_inst_3989_, lean_object* v_toBind_3990_, lean_object* v___f_3991_, lean_object* v_____do__lift_3992_){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3993_, 0, v_____do__lift_3992_);
lean_closure_set(v___x_3993_, 1, v_binderType_3988_);
v___x_3994_ = lean_apply_2(v_inst_3989_, lean_box(0), v___x_3993_);
v___x_3995_ = lean_apply_4(v_toBind_3990_, lean_box(0), lean_box(0), v___x_3994_, v___f_3991_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3996_, lean_object* v_toPure_3997_, lean_object* v_levels_x3f_3998_, lean_object* v_inst_3999_, lean_object* v_toBind_4000_, lean_object* v_a_4001_, lean_object* v_x_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_snd_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4024_; 
v_snd_4004_ = lean_ctor_get(v___y_4003_, 1);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___y_4003_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v___y_4003_, 0);
lean_dec(v_unused_4025_);
v___x_4006_ = v___y_4003_;
v_isShared_4007_ = v_isSharedCheck_4024_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_snd_4004_);
lean_dec(v___y_4003_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4024_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
if (lean_obj_tag(v_snd_4004_) == 6)
{
lean_object* v_binderType_4008_; lean_object* v_body_4009_; lean_object* v___f_4010_; 
lean_del_object(v___x_4006_);
v_binderType_4008_ = lean_ctor_get(v_snd_4004_, 1);
lean_inc_ref(v_binderType_4008_);
v_body_4009_ = lean_ctor_get(v_snd_4004_, 2);
lean_inc(v_toPure_3997_);
lean_inc(v___x_3996_);
lean_inc_ref(v_a_4001_);
lean_inc_ref(v_body_4009_);
v___f_4010_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_4010_, 0, v_body_4009_);
lean_closure_set(v___f_4010_, 1, v_a_4001_);
lean_closure_set(v___f_4010_, 2, v___x_3996_);
lean_closure_set(v___f_4010_, 3, v_toPure_3997_);
if (lean_obj_tag(v_levels_x3f_3998_) == 0)
{
lean_object* v___f_4011_; lean_object* v___f_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec(v___x_3996_);
v___f_4011_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4011_, 0, v_snd_4004_);
lean_closure_set(v___f_4011_, 1, v_toPure_3997_);
lean_closure_set(v___f_4011_, 2, v___f_4010_);
lean_inc(v_toBind_4000_);
lean_inc(v_inst_3999_);
v___f_4012_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_4012_, 0, v_binderType_4008_);
lean_closure_set(v___f_4012_, 1, v_inst_3999_);
lean_closure_set(v___f_4012_, 2, v_toBind_4000_);
lean_closure_set(v___f_4012_, 3, v___f_4011_);
v___x_4013_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_4013_, 0, v_a_4001_);
v___x_4014_ = lean_apply_2(v_inst_3999_, lean_box(0), v___x_4013_);
v___x_4015_ = lean_apply_4(v_toBind_4000_, lean_box(0), lean_box(0), v___x_4014_, v___f_4012_);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_inc_ref(v_body_4009_);
lean_dec_ref(v___f_4010_);
lean_dec_ref_known(v_snd_4004_, 3);
lean_dec_ref(v_binderType_4008_);
lean_dec(v_toBind_4000_);
lean_dec(v_inst_3999_);
v___x_4016_ = lean_box(0);
v___x_4017_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_4009_, v_a_4001_, v___x_3996_, v_toPure_3997_, v___x_4016_);
lean_dec_ref(v_a_4001_);
lean_dec_ref(v_body_4009_);
return v___x_4017_;
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
lean_dec_ref(v_a_4001_);
lean_dec(v_toBind_4000_);
lean_dec(v_inst_3999_);
lean_dec(v___x_3996_);
v___x_4018_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 0, v___x_4018_);
v___x_4020_ = v___x_4006_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4018_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_snd_4004_);
v___x_4020_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
v___x_4022_ = lean_apply_2(v_toPure_3997_, lean_box(0), v___x_4021_);
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_4026_, lean_object* v_toPure_4027_, lean_object* v_levels_x3f_4028_, lean_object* v_inst_4029_, lean_object* v_toBind_4030_, lean_object* v_a_4031_, lean_object* v_x_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_4026_, v_toPure_4027_, v_levels_x3f_4028_, v_inst_4029_, v_toBind_4030_, v_a_4031_, v_x_4032_, v___y_4033_);
lean_dec(v_levels_x3f_4028_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_4035_, lean_object* v_levels_x3f_4036_, lean_object* v_inst_4037_, lean_object* v_toBind_4038_, lean_object* v_params_4039_, lean_object* v_inst_4040_, lean_object* v___f_4041_, lean_object* v_val_4042_){
_start:
{
lean_object* v___x_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; size_t v_sz_4046_; size_t v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4043_ = lean_box(0);
lean_inc(v_toBind_4038_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_4044_, 0, v___x_4043_);
lean_closure_set(v___f_4044_, 1, v_toPure_4035_);
lean_closure_set(v___f_4044_, 2, v_levels_x3f_4036_);
lean_closure_set(v___f_4044_, 3, v_inst_4037_);
lean_closure_set(v___f_4044_, 4, v_toBind_4038_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v_val_4042_);
v_sz_4046_ = lean_array_size(v_params_4039_);
v___x_4047_ = ((size_t)0ULL);
v___x_4048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4040_, v_params_4039_, v___f_4044_, v_sz_4046_, v___x_4047_, v___x_4045_);
v___x_4049_ = lean_apply_4(v_toBind_4038_, lean_box(0), lean_box(0), v___x_4048_, v___f_4041_);
return v___x_4049_;
}
}
lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4050_, lean_object* v_us_4051_, uint8_t v___x_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4050_, v_us_4051_, v___x_4052_, v___y_4055_, v___y_4056_);
return v___x_4058_;
}
}
LEAN_EXPORT void l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cinfo_4050_ = stack[0].m_obj;
lean_object* v_us_4051_ = stack[1].m_obj;
uint8_t v___x_4052_ = stack[2].m_num;
lean_object* v___y_4053_ = stack[3].m_obj;
lean_object* v___y_4054_ = stack[4].m_obj;
lean_object* v___y_4055_ = stack[5].m_obj;
lean_object* v___y_4056_ = stack[6].m_obj;
lean_object* v_res_4059_;
v_res_4059_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4050_, v_us_4051_, v___x_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
stack->m_obj
 = v_res_4059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4060_, lean_object* v_us_4061_, lean_object* v___x_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
uint8_t v___x_751__boxed_4068_; lean_object* v_res_4069_; 
v___x_751__boxed_4068_ = lean_unbox(v___x_4062_);
v_res_4069_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4060_, v_us_4061_, v___x_751__boxed_4068_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec_ref(v_cinfo_4060_);
return v_res_4069_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4073_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4074_ = lean_unsigned_to_nat(2u);
v___x_4075_ = lean_unsigned_to_nat(202u);
v___x_4076_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4077_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4078_ = l_mkPanicMessageWithDecl(v___x_4077_, v___x_4076_, v___x_4075_, v___x_4074_, v___x_4073_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4079_, lean_object* v___x_4080_, lean_object* v_inst_4081_, lean_object* v_toBind_4082_, lean_object* v___f_4083_, lean_object* v_us_4084_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; 
v___x_4085_ = l_List_lengthTR___redArg(v_us_4084_);
v___x_4086_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4079_);
v___x_4087_ = l_List_lengthTR___redArg(v___x_4086_);
lean_dec(v___x_4086_);
v___x_4088_ = lean_nat_dec_eq(v___x_4085_, v___x_4087_);
lean_dec(v___x_4087_);
lean_dec(v___x_4085_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec(v_us_4084_);
lean_dec(v___f_4083_);
lean_dec(v_toBind_4082_);
lean_dec(v_inst_4081_);
lean_dec_ref(v_cinfo_4079_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4090_ = l_panic___redArg(v___x_4080_, v___x_4089_);
return v___x_4090_;
}
else
{
uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___f_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4091_ = 0;
v___x_4092_ = lean_box(v___x_4091_);
v___f_4093_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4093_, 0, v_cinfo_4079_);
lean_closure_set(v___f_4093_, 1, v_us_4084_);
lean_closure_set(v___f_4093_, 2, v___x_4092_);
v___x_4094_ = lean_apply_2(v_inst_4081_, lean_box(0), v___f_4093_);
v___x_4095_ = lean_apply_4(v_toBind_4082_, lean_box(0), lean_box(0), v___x_4094_, v___f_4083_);
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4096_, lean_object* v___x_4097_, lean_object* v_inst_4098_, lean_object* v_toBind_4099_, lean_object* v___f_4100_, lean_object* v_us_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4096_, v___x_4097_, v_inst_4098_, v_toBind_4099_, v___f_4100_, v_us_4101_);
lean_dec(v___x_4097_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4103_, lean_object* v_inst_4104_, lean_object* v_toBind_4105_, lean_object* v___f_4106_, lean_object* v_levels_x3f_4107_, lean_object* v_toPure_4108_, lean_object* v_cinfo_4109_){
_start:
{
lean_object* v___f_4110_; 
lean_inc(v_toBind_4105_);
lean_inc(v_inst_4104_);
lean_inc_ref(v_cinfo_4109_);
v___f_4110_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4110_, 0, v_cinfo_4109_);
lean_closure_set(v___f_4110_, 1, v___x_4103_);
lean_closure_set(v___f_4110_, 2, v_inst_4104_);
lean_closure_set(v___f_4110_, 3, v_toBind_4105_);
lean_closure_set(v___f_4110_, 4, v___f_4106_);
if (lean_obj_tag(v_levels_x3f_4107_) == 0)
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec(v_toPure_4108_);
v___x_4111_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4111_, 0, v_cinfo_4109_);
v___x_4112_ = lean_apply_2(v_inst_4104_, lean_box(0), v___x_4111_);
v___x_4113_ = lean_apply_4(v_toBind_4105_, lean_box(0), lean_box(0), v___x_4112_, v___f_4110_);
return v___x_4113_;
}
else
{
lean_object* v_val_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec_ref(v_cinfo_4109_);
lean_dec(v_inst_4104_);
v_val_4114_ = lean_ctor_get(v_levels_x3f_4107_, 0);
lean_inc(v_val_4114_);
lean_dec_ref_known(v_levels_x3f_4107_, 1);
v___x_4115_ = lean_apply_2(v_toPure_4108_, lean_box(0), v_val_4114_);
v___x_4116_ = lean_apply_4(v_toBind_4105_, lean_box(0), lean_box(0), v___x_4115_, v___f_4110_);
return v___x_4116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4117_, lean_object* v_inst_4118_, lean_object* v_inst_4119_, lean_object* v_inst_4120_, lean_object* v_defaultFn_4121_, lean_object* v_levels_x3f_4122_, lean_object* v_params_4123_, lean_object* v_fieldVal_x3f_4124_){
_start:
{
lean_object* v_toApplicative_4125_; lean_object* v_toBind_4126_; lean_object* v_toPure_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___f_4130_; lean_object* v___f_4131_; lean_object* v___x_4132_; lean_object* v___f_4133_; lean_object* v___x_4134_; 
v_toApplicative_4125_ = lean_ctor_get(v_inst_4117_, 0);
v_toBind_4126_ = lean_ctor_get(v_inst_4117_, 1);
lean_inc_n(v_toBind_4126_, 3);
v_toPure_4127_ = lean_ctor_get(v_toApplicative_4125_, 1);
lean_inc_n(v_toPure_4127_, 3);
v___x_4128_ = lean_box(0);
lean_inc_ref_n(v_inst_4117_, 3);
v___x_4129_ = l_Lean_getConstInfo___redArg(v_inst_4117_, v_inst_4118_, v_inst_4119_, v_defaultFn_4121_);
lean_inc_n(v_inst_4120_, 2);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4130_, 0, v_inst_4117_);
lean_closure_set(v___f_4130_, 1, v_inst_4120_);
lean_closure_set(v___f_4130_, 2, v_fieldVal_x3f_4124_);
lean_closure_set(v___f_4130_, 3, v_toPure_4127_);
lean_inc(v_levels_x3f_4122_);
v___f_4131_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4131_, 0, v_toPure_4127_);
lean_closure_set(v___f_4131_, 1, v_levels_x3f_4122_);
lean_closure_set(v___f_4131_, 2, v_inst_4120_);
lean_closure_set(v___f_4131_, 3, v_toBind_4126_);
lean_closure_set(v___f_4131_, 4, v_params_4123_);
lean_closure_set(v___f_4131_, 5, v_inst_4117_);
lean_closure_set(v___f_4131_, 6, v___f_4130_);
v___x_4132_ = l_instInhabitedOfMonad___redArg(v_inst_4117_, v___x_4128_);
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4133_, 0, v___x_4132_);
lean_closure_set(v___f_4133_, 1, v_inst_4120_);
lean_closure_set(v___f_4133_, 2, v_toBind_4126_);
lean_closure_set(v___f_4133_, 3, v___f_4131_);
lean_closure_set(v___f_4133_, 4, v_levels_x3f_4122_);
lean_closure_set(v___f_4133_, 5, v_toPure_4127_);
v___x_4134_ = lean_apply_4(v_toBind_4126_, lean_box(0), lean_box(0), v___x_4129_, v___f_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4135_, lean_object* v_inst_4136_, lean_object* v_inst_4137_, lean_object* v_inst_4138_, lean_object* v_inst_4139_, lean_object* v_inst_4140_, lean_object* v_defaultFn_4141_, lean_object* v_levels_x3f_4142_, lean_object* v_params_4143_, lean_object* v_fieldVal_x3f_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4136_, v_inst_4137_, v_inst_4138_, v_inst_4139_, v_defaultFn_4141_, v_levels_x3f_4142_, v_params_4143_, v_fieldVal_x3f_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4146_, lean_object* v_inst_4147_, lean_object* v_inst_4148_, lean_object* v_inst_4149_, lean_object* v_inst_4150_, lean_object* v_inst_4151_, lean_object* v_defaultFn_4152_, lean_object* v_levels_x3f_4153_, lean_object* v_params_4154_, lean_object* v_fieldVal_x3f_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4146_, v_inst_4147_, v_inst_4148_, v_inst_4149_, v_inst_4150_, v_inst_4151_, v_defaultFn_4152_, v_levels_x3f_4153_, v_params_4154_, v_fieldVal_x3f_4155_);
lean_dec_ref(v_inst_4151_);
return v_res_4156_;
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
