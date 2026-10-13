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
lean_object* v___x_117_; uint8_t v___y_119_; uint8_t v___y_126_; lean_object* v_env_129_; uint8_t v___x_130_; 
v___x_117_ = lean_st_ref_get(v___y_115_);
v_env_129_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref_n(v_env_129_, 2);
lean_dec(v___x_117_);
v___x_130_ = l_Lean_Environment_hasUnsafe(v_env_129_, v_type_112_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Environment_hasUnsafe(v_env_129_, v_value_113_);
v___y_126_ = v___x_131_;
goto v___jp_125_;
}
else
{
lean_dec_ref(v_env_129_);
v___y_126_ = v___x_130_;
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
if (v___y_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 1;
v___y_119_ = v___x_127_;
goto v___jp_118_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
v___y_119_ = v___x_128_;
goto v___jp_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v_name_132_, lean_object* v_levelParams_133_, lean_object* v_type_134_, lean_object* v_value_135_, lean_object* v_hints_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_132_, v_levelParams_133_, v_type_134_, v_value_135_, v_hints_136_, v___y_137_);
lean_dec(v___y_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_name_140_, lean_object* v_levelParams_141_, lean_object* v_type_142_, lean_object* v_value_143_, lean_object* v_hints_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_name_140_, v_levelParams_141_, v_type_142_, v_value_143_, v_hints_144_, v___y_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(lean_object* v_name_151_, lean_object* v_levelParams_152_, lean_object* v_type_153_, lean_object* v_value_154_, lean_object* v_hints_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(v_name_151_, v_levelParams_152_, v_type_153_, v_value_154_, v_hints_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v_k_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
v___x_169_ = lean_apply_6(v_k_162_, v_b_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object* v_k_170_, lean_object* v_b_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v_k_170_, v_b_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_name_178_, uint8_t v_bi_179_, lean_object* v_type_180_, lean_object* v_k_181_, uint8_t v_kind_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; 
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_188_, 0, v_k_181_);
v___x_189_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_178_, v_bi_179_, v_type_180_, v___f_188_, v_kind_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_189_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_189_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object* v_name_206_, lean_object* v_bi_207_, lean_object* v_type_208_, lean_object* v_k_209_, lean_object* v_kind_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v_bi_boxed_216_; uint8_t v_kind_boxed_217_; lean_object* v_res_218_; 
v_bi_boxed_216_ = lean_unbox(v_bi_207_);
v_kind_boxed_217_ = lean_unbox(v_kind_210_);
v_res_218_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_206_, v_bi_boxed_216_, v_type_208_, v_k_209_, v_kind_boxed_217_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_00_u03b1_219_, lean_object* v_name_220_, uint8_t v_bi_221_, lean_object* v_type_222_, lean_object* v_k_223_, uint8_t v_kind_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v_name_220_, v_bi_221_, v_type_222_, v_k_223_, v_kind_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object* v_00_u03b1_231_, lean_object* v_name_232_, lean_object* v_bi_233_, lean_object* v_type_234_, lean_object* v_k_235_, lean_object* v_kind_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_bi_boxed_242_; uint8_t v_kind_boxed_243_; lean_object* v_res_244_; 
v_bi_boxed_242_ = lean_unbox(v_bi_233_);
v_kind_boxed_243_ = lean_unbox(v_kind_236_);
v_res_244_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(v_00_u03b1_231_, v_name_232_, v_bi_boxed_242_, v_type_234_, v_k_235_, v_kind_boxed_243_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_245_, lean_object* v_b_246_, lean_object* v_c_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_253_ = lean_apply_7(v_k_245_, v_b_246_, v_c_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_254_, lean_object* v_b_255_, lean_object* v_c_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_254_, v_b_255_, v_c_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_type_263_, lean_object* v_maxFVars_x3f_264_, lean_object* v_k_265_, uint8_t v_cleanupAnnotations_266_, uint8_t v_whnfType_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_274_; 
v___f_273_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_273_, 0, v_k_265_);
v___x_274_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_263_, v_maxFVars_x3f_264_, v___f_273_, v_cleanupAnnotations_266_, v_whnfType_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_274_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_274_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_type_291_, lean_object* v_maxFVars_x3f_292_, lean_object* v_k_293_, lean_object* v_cleanupAnnotations_294_, lean_object* v_whnfType_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_301_; uint8_t v_whnfType_boxed_302_; lean_object* v_res_303_; 
v_cleanupAnnotations_boxed_301_ = lean_unbox(v_cleanupAnnotations_294_);
v_whnfType_boxed_302_ = lean_unbox(v_whnfType_295_);
v_res_303_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_291_, v_maxFVars_x3f_292_, v_k_293_, v_cleanupAnnotations_boxed_301_, v_whnfType_boxed_302_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_304_, lean_object* v_type_305_, lean_object* v_maxFVars_x3f_306_, lean_object* v_k_307_, uint8_t v_cleanupAnnotations_308_, uint8_t v_whnfType_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_305_, v_maxFVars_x3f_306_, v_k_307_, v_cleanupAnnotations_308_, v_whnfType_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_316_, lean_object* v_type_317_, lean_object* v_maxFVars_x3f_318_, lean_object* v_k_319_, lean_object* v_cleanupAnnotations_320_, lean_object* v_whnfType_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_327_; uint8_t v_whnfType_boxed_328_; lean_object* v_res_329_; 
v_cleanupAnnotations_boxed_327_ = lean_unbox(v_cleanupAnnotations_320_);
v_whnfType_boxed_328_ = lean_unbox(v_whnfType_321_);
v_res_329_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_316_, v_type_317_, v_maxFVars_x3f_318_, v_k_319_, v_cleanupAnnotations_boxed_327_, v_whnfType_boxed_328_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_lctx_330_, lean_object* v_localInsts_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_330_, v_localInsts_331_, v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_338_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_338_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_lctx_355_, lean_object* v_localInsts_356_, lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_355_, v_localInsts_356_, v_x_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_364_, lean_object* v_lctx_365_, lean_object* v_localInsts_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v_lctx_365_, v_localInsts_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_374_, lean_object* v_lctx_375_, lean_object* v_localInsts_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_374_, v_lctx_375_, v_localInsts_376_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(lean_object* v_ref_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_toCold_391_; lean_object* v_currRecDepth_392_; lean_object* v_ref_393_; uint16_t v_optionFlags_394_; uint8_t v_suppressElabErrors_395_; uint8_t v_isRecordingDeps_396_; lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_toCold_391_ = lean_ctor_get(v___y_388_, 0);
v_currRecDepth_392_ = lean_ctor_get(v___y_388_, 1);
v_ref_393_ = lean_ctor_get(v___y_388_, 2);
v_optionFlags_394_ = lean_ctor_get_uint16(v___y_388_, sizeof(void*)*3);
v_suppressElabErrors_395_ = lean_ctor_get_uint8(v___y_388_, sizeof(void*)*3 + 2);
v_isRecordingDeps_396_ = lean_ctor_get_uint8(v___y_388_, sizeof(void*)*3 + 3);
v_ref_397_ = l_Lean_replaceRef(v_ref_384_, v_ref_393_);
lean_inc(v_currRecDepth_392_);
lean_inc_ref(v_toCold_391_);
v___x_398_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_398_, 0, v_toCold_391_);
lean_ctor_set(v___x_398_, 1, v_currRecDepth_392_);
lean_ctor_set(v___x_398_, 2, v_ref_397_);
lean_ctor_set_uint16(v___x_398_, sizeof(void*)*3, v_optionFlags_394_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 2, v_suppressElabErrors_395_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3 + 3, v_isRecordingDeps_396_);
v___x_399_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_385_, v___y_386_, v___y_387_, v___x_398_, v___y_389_);
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
uint8_t v___x_17048__boxed_459_; lean_object* v_res_460_; 
v___x_17048__boxed_459_ = lean_unbox(v___x_449_);
v_res_460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17048__boxed_459_, v_projName_450_, v_n_451_, v_ref_452_, v___f_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
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
v___x_467_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v___x_466_);
lean_ctor_set(v___x_467_, 4, v___x_466_);
lean_ctor_set(v___x_467_, 5, v___x_466_);
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
lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; uint8_t v___y_631_; uint8_t v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = l_List_lengthTR___redArg(v_paramInfoOverrides_556_);
v___x_722_ = lean_array_get_size(v_params_550_);
v___x_723_ = lean_nat_dec_le(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_724_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_545_);
v___x_725_ = l_Lean_MessageData_ofName(v_projName_545_);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_inc(v_n_557_);
v___x_729_ = l_Lean_MessageData_ofConstName(v_n_557_, v___x_723_);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_558_, v___x_732_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref_known(v___x_733_, 1);
goto v___jp_682_;
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
goto v___jp_682_;
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
lean_ctor_set(v___x_634_, 0, v___y_629_);
lean_ctor_set(v___x_634_, 1, v___y_628_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*3, v___x_553_);
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = l_Lean_addDecl(v___x_635_, v___y_631_, v___y_627_, v___y_630_);
lean_dec_ref(v___y_627_);
v___y_614_ = v___y_626_;
v___y_615_ = v___y_630_;
v___y_616_ = v___x_636_;
goto v___jp_613_;
}
v___jp_637_:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v_toCold_646_; lean_object* v_currRecDepth_647_; lean_object* v_ref_648_; uint16_t v_optionFlags_649_; uint8_t v_suppressElabErrors_650_; uint8_t v_isRecordingDeps_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v_ref_656_; lean_object* v___x_657_; 
v___x_644_ = 0;
lean_inc_ref(v_a_554_);
v___x_645_ = l_Lean_LocalContext_mkForall(v_a_554_, v___x_555_, v___y_639_, v___x_553_, v___x_644_);
lean_dec_ref(v___y_639_);
v_toCold_646_ = lean_ctor_get(v___y_642_, 0);
v_currRecDepth_647_ = lean_ctor_get(v___y_642_, 1);
v_ref_648_ = lean_ctor_get(v___y_642_, 2);
v_optionFlags_649_ = lean_ctor_get_uint16(v___y_642_, sizeof(void*)*3);
v_suppressElabErrors_650_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*3 + 2);
v_isRecordingDeps_651_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*3 + 3);
v___x_652_ = l_Lean_Expr_inferImplicit(v___x_645_, v___x_546_, v___x_553_);
v___x_653_ = l_Lean_Expr_updateForallBinderInfos(v___x_652_, v_paramInfoOverrides_556_);
lean_inc_ref(v_self_551_);
lean_inc(v_a_547_);
v___x_654_ = l_Lean_Expr_proj___override(v_n_557_, v_a_547_, v_self_551_);
v___x_655_ = l_Lean_LocalContext_mkLambda(v_a_554_, v___x_555_, v___x_654_, v___x_553_, v___x_644_);
lean_dec_ref(v___x_654_);
v_ref_656_ = l_Lean_replaceRef(v_ref_558_, v_ref_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_toCold_646_);
v___x_657_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_657_, 0, v_toCold_646_);
lean_ctor_set(v___x_657_, 1, v_currRecDepth_647_);
lean_ctor_set(v___x_657_, 2, v_ref_656_);
lean_ctor_set_uint16(v___x_657_, sizeof(void*)*3, v_optionFlags_649_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*3 + 2, v_suppressElabErrors_650_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*3 + 3, v_isRecordingDeps_651_);
if (v___y_638_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(1);
lean_inc(v_projName_545_);
v___x_659_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_545_, v___x_559_, v___x_653_, v___x_655_, v___x_658_, v___y_643_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_a_660_);
v___x_662_ = l_Lean_addDecl(v___x_661_, v___x_644_, v___x_657_, v___y_643_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_dec_ref_known(v___x_662_, 1);
if (v_instImplicit_548_ == 0)
{
lean_object* v___x_663_; 
lean_inc(v_projName_545_);
v___x_663_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_545_, v___y_640_, v___y_641_, v___x_657_, v___y_643_);
lean_dec_ref_known(v___x_657_, 3);
v___y_614_ = v___y_641_;
v___y_615_ = v___y_643_;
v___y_616_ = v___x_663_;
goto v___jp_613_;
}
else
{
lean_dec_ref_known(v___x_657_, 3);
v___y_568_ = v___y_641_;
v___y_569_ = v___y_643_;
goto v___jp_567_;
}
}
else
{
lean_dec_ref_known(v___x_657_, 3);
v___y_614_ = v___y_641_;
v___y_615_ = v___y_643_;
v___y_616_ = v___x_662_;
goto v___jp_613_;
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref_known(v___x_657_, 3);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_664_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_659_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_659_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_env_674_; uint8_t v___x_675_; 
lean_inc_ref(v___x_653_);
lean_inc(v_projName_545_);
v___x_672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_672_, 0, v_projName_545_);
lean_ctor_set(v___x_672_, 1, v___x_559_);
lean_ctor_set(v___x_672_, 2, v___x_653_);
v___x_673_ = lean_st_ref_get(v___y_643_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref_n(v_env_674_, 2);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_Environment_hasUnsafe(v_env_674_, v___x_653_);
lean_dec_ref(v___x_653_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = l_Lean_Environment_hasUnsafe(v_env_674_, v___x_655_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = lean_box(0);
lean_inc(v_projName_545_);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v_projName_545_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_672_);
lean_ctor_set(v___x_679_, 1, v___x_655_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
v___x_680_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
v___x_681_ = l_Lean_addDecl(v___x_680_, v___x_644_, v___x_657_, v___y_643_);
lean_dec_ref_known(v___x_657_, 3);
v___y_614_ = v___y_641_;
v___y_615_ = v___y_643_;
v___y_616_ = v___x_681_;
goto v___jp_613_;
}
else
{
v___y_626_ = v___y_641_;
v___y_627_ = v___x_657_;
v___y_628_ = v___x_655_;
v___y_629_ = v___x_672_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_644_;
goto v___jp_625_;
}
}
else
{
lean_dec_ref(v_env_674_);
v___y_626_ = v___y_641_;
v___y_627_ = v___x_657_;
v___y_628_ = v___x_655_;
v___y_629_ = v___x_672_;
v___y_630_ = v___y_643_;
v___y_631_ = v___x_644_;
goto v___jp_625_;
}
}
}
v___jp_682_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = l_Lean_Expr_bindingDomain_x21(v_b_552_);
v___x_684_ = lean_expr_consume_type_annotations(v___x_683_);
lean_inc_ref(v___x_684_);
v___x_685_ = l_Lean_Meta_isProp(v___x_684_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_685_) == 0)
{
if (v_a_560_ == 0)
{
lean_object* v_a_686_; uint8_t v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = lean_unbox(v_a_686_);
lean_dec(v_a_686_);
v___y_638_ = v___x_687_;
v___y_639_ = v___x_684_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
v___y_643_ = v___y_565_;
goto v___jp_637_;
}
else
{
lean_object* v_a_688_; uint8_t v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_685_, 1);
v___x_689_ = lean_unbox(v_a_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_690_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_545_);
v___x_691_ = l_Lean_MessageData_ofName(v_projName_545_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_unbox(v_a_688_);
lean_inc(v_n_557_);
v___x_696_ = l_Lean_MessageData_ofConstName(v_n_557_, v___x_695_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_inc_ref(v___x_684_);
v___x_700_ = l_Lean_indentExpr(v___x_684_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_558_, v___x_701_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_702_) == 0)
{
uint8_t v___x_703_; 
lean_dec_ref_known(v___x_702_, 1);
v___x_703_ = lean_unbox(v_a_688_);
lean_dec(v_a_688_);
v___y_638_ = v___x_703_;
v___y_639_ = v___x_684_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
v___y_643_ = v___y_565_;
goto v___jp_637_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_a_688_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_704_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_702_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
uint8_t v___x_712_; 
v___x_712_ = lean_unbox(v_a_688_);
lean_dec(v_a_688_);
v___y_638_ = v___x_712_;
v___y_639_ = v___x_684_;
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
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v___x_684_);
lean_dec(v___x_559_);
lean_dec(v_n_557_);
lean_dec_ref(v_a_554_);
lean_dec_ref(v_self_551_);
lean_dec(v___x_549_);
lean_dec(v_a_547_);
lean_dec(v___x_546_);
lean_dec(v_projName_545_);
lean_dec_ref(v___x_544_);
v_a_713_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_685_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_685_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_742_ = _args[0];
lean_object* v_projName_743_ = _args[1];
lean_object* v___x_744_ = _args[2];
lean_object* v_a_745_ = _args[3];
lean_object* v_instImplicit_746_ = _args[4];
lean_object* v___x_747_ = _args[5];
lean_object* v_params_748_ = _args[6];
lean_object* v_self_749_ = _args[7];
lean_object* v_b_750_ = _args[8];
lean_object* v___x_751_ = _args[9];
lean_object* v_a_752_ = _args[10];
lean_object* v___x_753_ = _args[11];
lean_object* v_paramInfoOverrides_754_ = _args[12];
lean_object* v_n_755_ = _args[13];
lean_object* v_ref_756_ = _args[14];
lean_object* v___x_757_ = _args[15];
lean_object* v_a_758_ = _args[16];
lean_object* v_____r_759_ = _args[17];
lean_object* v___y_760_ = _args[18];
lean_object* v___y_761_ = _args[19];
lean_object* v___y_762_ = _args[20];
lean_object* v___y_763_ = _args[21];
lean_object* v___y_764_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_765_; uint8_t v___x_17287__boxed_766_; uint8_t v_a_17293__boxed_767_; lean_object* v_res_768_; 
v_instImplicit_boxed_765_ = lean_unbox(v_instImplicit_746_);
v___x_17287__boxed_766_ = lean_unbox(v___x_751_);
v_a_17293__boxed_767_ = lean_unbox(v_a_758_);
v_res_768_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_742_, v_projName_743_, v___x_744_, v_a_745_, v_instImplicit_boxed_765_, v___x_747_, v_params_748_, v_self_749_, v_b_750_, v___x_17287__boxed_766_, v_a_752_, v___x_753_, v_paramInfoOverrides_754_, v_n_755_, v_ref_756_, v___x_757_, v_a_17293__boxed_767_, v_____r_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_ref_756_);
lean_dec(v_paramInfoOverrides_754_);
lean_dec_ref(v___x_753_);
lean_dec_ref(v_b_750_);
lean_dec_ref(v_params_748_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(lean_object* v___y_769_, uint8_t v_isExporting_770_, lean_object* v___x_771_, lean_object* v___y_772_, lean_object* v___x_773_, lean_object* v_a_x3f_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_env_777_; lean_object* v_nextMacroScope_778_; lean_object* v_ngen_779_; lean_object* v_auxDeclNGen_780_; lean_object* v_traceState_781_; lean_object* v_recordedDeps_782_; lean_object* v_messages_783_; lean_object* v_infoState_784_; lean_object* v_snapshotTasks_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_810_; 
v___x_776_ = lean_st_ref_take(v___y_769_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
v_nextMacroScope_778_ = lean_ctor_get(v___x_776_, 1);
v_ngen_779_ = lean_ctor_get(v___x_776_, 2);
v_auxDeclNGen_780_ = lean_ctor_get(v___x_776_, 3);
v_traceState_781_ = lean_ctor_get(v___x_776_, 4);
v_recordedDeps_782_ = lean_ctor_get(v___x_776_, 6);
v_messages_783_ = lean_ctor_get(v___x_776_, 7);
v_infoState_784_ = lean_ctor_get(v___x_776_, 8);
v_snapshotTasks_785_ = lean_ctor_get(v___x_776_, 9);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_776_, 5);
lean_dec(v_unused_811_);
v___x_787_ = v___x_776_;
v_isShared_788_ = v_isSharedCheck_810_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snapshotTasks_785_);
lean_inc(v_infoState_784_);
lean_inc(v_messages_783_);
lean_inc(v_recordedDeps_782_);
lean_inc(v_traceState_781_);
lean_inc(v_auxDeclNGen_780_);
lean_inc(v_ngen_779_);
lean_inc(v_nextMacroScope_778_);
lean_inc(v_env_777_);
lean_dec(v___x_776_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_810_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = l_Lean_Environment_setExporting(v_env_777_, v_isExporting_770_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 5, v___x_771_);
lean_ctor_set(v___x_787_, 0, v___x_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_nextMacroScope_778_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_ngen_779_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_auxDeclNGen_780_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_traceState_781_);
lean_ctor_set(v_reuseFailAlloc_809_, 5, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_809_, 6, v_recordedDeps_782_);
lean_ctor_set(v_reuseFailAlloc_809_, 7, v_messages_783_);
lean_ctor_set(v_reuseFailAlloc_809_, 8, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_809_, 9, v_snapshotTasks_785_);
v___x_791_ = v_reuseFailAlloc_809_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_mctx_794_; lean_object* v_zetaDeltaFVarIds_795_; lean_object* v_postponed_796_; lean_object* v_diag_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_807_; 
v___x_792_ = lean_st_ref_put(v___y_769_, v___x_791_);
v___x_793_ = lean_st_ref_take(v___y_772_);
v_mctx_794_ = lean_ctor_get(v___x_793_, 0);
v_zetaDeltaFVarIds_795_ = lean_ctor_get(v___x_793_, 2);
v_postponed_796_ = lean_ctor_get(v___x_793_, 3);
v_diag_797_ = lean_ctor_get(v___x_793_, 4);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_808_);
v___x_799_ = v___x_793_;
v_isShared_800_ = v_isSharedCheck_807_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_diag_797_);
lean_inc(v_postponed_796_);
lean_inc(v_zetaDeltaFVarIds_795_);
lean_inc(v_mctx_794_);
lean_dec(v___x_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_807_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_773_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_mctx_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_zetaDeltaFVarIds_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_postponed_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_diag_797_);
v___x_803_ = v_reuseFailAlloc_806_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_st_ref_put(v___y_772_, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_801_);
return v___x_805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_812_, lean_object* v_isExporting_813_, lean_object* v___x_814_, lean_object* v___y_815_, lean_object* v___x_816_, lean_object* v_a_x3f_817_, lean_object* v___y_818_){
_start:
{
uint8_t v_isExporting_boxed_819_; lean_object* v_res_820_; 
v_isExporting_boxed_819_ = lean_unbox(v_isExporting_813_);
v_res_820_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_812_, v_isExporting_boxed_819_, v___x_814_, v___y_815_, v___x_816_, v_a_x3f_817_);
lean_dec(v_a_x3f_817_);
lean_dec(v___y_815_);
lean_dec(v___y_812_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_821_, uint8_t v_isExporting_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_env_829_; lean_object* v___x_830_; uint8_t v_isModule_831_; 
v___x_828_ = lean_st_ref_get(v___y_826_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_env_829_);
lean_dec(v___x_828_);
v___x_830_ = l_Lean_Environment_header(v_env_829_);
v_isModule_831_ = lean_ctor_get_uint8(v___x_830_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_830_);
if (v_isModule_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_env_829_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v___x_832_ = lean_apply_5(v_x_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
return v___x_832_;
}
else
{
uint8_t v_isExporting_833_; 
v_isExporting_833_ = lean_ctor_get_uint8(v_env_829_, sizeof(void*)*13);
lean_dec_ref(v_env_829_);
if (v_isExporting_822_ == 0)
{
if (v_isExporting_833_ == 0)
{
lean_object* v___x_900_; 
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v___x_900_ = lean_apply_5(v_x_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
return v___x_900_;
}
else
{
goto v___jp_834_;
}
}
else
{
if (v_isExporting_833_ == 0)
{
goto v___jp_834_;
}
else
{
lean_object* v___x_901_; 
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v___x_901_ = lean_apply_5(v_x_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
return v___x_901_;
}
}
v___jp_834_:
{
lean_object* v___x_835_; lean_object* v_env_836_; lean_object* v_nextMacroScope_837_; lean_object* v_ngen_838_; lean_object* v_auxDeclNGen_839_; lean_object* v_traceState_840_; lean_object* v_recordedDeps_841_; lean_object* v_messages_842_; lean_object* v_infoState_843_; lean_object* v_snapshotTasks_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_898_; 
v___x_835_ = lean_st_ref_take(v___y_826_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
v_nextMacroScope_837_ = lean_ctor_get(v___x_835_, 1);
v_ngen_838_ = lean_ctor_get(v___x_835_, 2);
v_auxDeclNGen_839_ = lean_ctor_get(v___x_835_, 3);
v_traceState_840_ = lean_ctor_get(v___x_835_, 4);
v_recordedDeps_841_ = lean_ctor_get(v___x_835_, 6);
v_messages_842_ = lean_ctor_get(v___x_835_, 7);
v_infoState_843_ = lean_ctor_get(v___x_835_, 8);
v_snapshotTasks_844_ = lean_ctor_get(v___x_835_, 9);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v___x_835_, 5);
lean_dec(v_unused_899_);
v___x_846_ = v___x_835_;
v_isShared_847_ = v_isSharedCheck_898_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_snapshotTasks_844_);
lean_inc(v_infoState_843_);
lean_inc(v_messages_842_);
lean_inc(v_recordedDeps_841_);
lean_inc(v_traceState_840_);
lean_inc(v_auxDeclNGen_839_);
lean_inc(v_ngen_838_);
lean_inc(v_nextMacroScope_837_);
lean_inc(v_env_836_);
lean_dec(v___x_835_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_898_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = l_Lean_Environment_setExporting(v_env_836_, v_isExporting_822_);
v___x_849_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 5, v___x_849_);
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_nextMacroScope_837_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_ngen_838_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_auxDeclNGen_839_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_traceState_840_);
lean_ctor_set(v_reuseFailAlloc_897_, 5, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_897_, 6, v_recordedDeps_841_);
lean_ctor_set(v_reuseFailAlloc_897_, 7, v_messages_842_);
lean_ctor_set(v_reuseFailAlloc_897_, 8, v_infoState_843_);
lean_ctor_set(v_reuseFailAlloc_897_, 9, v_snapshotTasks_844_);
v___x_851_ = v_reuseFailAlloc_897_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_mctx_854_; lean_object* v_zetaDeltaFVarIds_855_; lean_object* v_postponed_856_; lean_object* v_diag_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_895_; 
v___x_852_ = lean_st_ref_put(v___y_826_, v___x_851_);
v___x_853_ = lean_st_ref_take(v___y_824_);
v_mctx_854_ = lean_ctor_get(v___x_853_, 0);
v_zetaDeltaFVarIds_855_ = lean_ctor_get(v___x_853_, 2);
v_postponed_856_ = lean_ctor_get(v___x_853_, 3);
v_diag_857_ = lean_ctor_get(v___x_853_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_853_, 1);
lean_dec(v_unused_896_);
v___x_859_ = v___x_853_;
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_diag_857_);
lean_inc(v_postponed_856_);
lean_inc(v_zetaDeltaFVarIds_855_);
lean_inc(v_mctx_854_);
lean_dec(v___x_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_mctx_854_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_zetaDeltaFVarIds_855_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_postponed_856_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_diag_857_);
v___x_863_ = v_reuseFailAlloc_894_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v_r_865_; 
v___x_864_ = lean_st_ref_put(v___y_824_, v___x_863_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v___y_824_);
lean_inc_ref(v___y_823_);
v_r_865_ = lean_apply_5(v_x_821_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, lean_box(0));
if (lean_obj_tag(v_r_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_882_; 
v_a_866_ = lean_ctor_get(v_r_865_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_r_865_);
if (v_isSharedCheck_882_ == 0)
{
v___x_868_ = v_r_865_;
v_isShared_869_ = v_isSharedCheck_882_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v_r_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_882_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
lean_inc(v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 1);
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_881_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v___x_872_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_826_, v_isExporting_833_, v___x_849_, v___y_824_, v___x_861_, v___x_871_);
lean_dec_ref(v___x_871_);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_872_, 0);
lean_dec(v_unused_880_);
v___x_874_ = v___x_872_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_dec(v___x_872_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_a_866_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_866_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_883_ = lean_ctor_get(v_r_865_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v_r_865_, 1);
v___x_884_ = lean_box(0);
v___x_885_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_826_, v_isExporting_833_, v___x_849_, v___y_824_, v___x_861_, v___x_884_);
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
lean_ctor_set_tag(v___x_887_, 1);
lean_ctor_set(v___x_887_, 0, v_a_883_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_883_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_902_, lean_object* v_isExporting_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
uint8_t v_isExporting_boxed_909_; lean_object* v_res_910_; 
v_isExporting_boxed_909_ = lean_unbox(v_isExporting_903_);
v_res_910_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_902_, v_isExporting_boxed_909_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_911_, uint8_t v_when_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
if (v_when_912_ == 0)
{
lean_object* v___x_918_; 
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
v___x_918_ = lean_apply_5(v_x_911_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, lean_box(0));
return v___x_918_;
}
else
{
uint8_t v___x_919_; lean_object* v___x_920_; 
v___x_919_ = 0;
v___x_920_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_911_, v___x_919_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_921_, lean_object* v_when_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_when_boxed_928_; lean_object* v_res_929_; 
v_when_boxed_928_ = lean_unbox(v_when_922_);
v_res_929_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_921_, v_when_boxed_928_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_930_, lean_object* v_projDecls_931_, lean_object* v___x_932_, lean_object* v___x_933_, uint8_t v_instImplicit_934_, lean_object* v___x_935_, lean_object* v_params_936_, lean_object* v_self_937_, lean_object* v_a_938_, lean_object* v___x_939_, lean_object* v_n_940_, lean_object* v___x_941_, uint8_t v_a_942_, lean_object* v_a_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_nat_dec_lt(v_a_943_, v_upperBound_930_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec(v_a_943_);
lean_dec(v___x_941_);
lean_dec(v_n_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_a_938_);
lean_dec_ref(v_self_937_);
lean_dec_ref(v_params_936_);
lean_dec(v___x_935_);
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_944_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v_ref_953_; lean_object* v_projName_954_; lean_object* v_paramInfoOverrides_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___f_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___y_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v___x_952_ = lean_array_fget_borrowed(v_projDecls_931_, v_a_943_);
v_ref_953_ = lean_ctor_get(v___x_952_, 0);
v_projName_954_ = lean_ctor_get(v___x_952_, 1);
v_paramInfoOverrides_955_ = lean_ctor_get(v___x_952_, 2);
v___x_956_ = lean_box(v_instImplicit_934_);
v___x_957_ = lean_box(v___x_950_);
v___x_958_ = lean_box(v_a_942_);
lean_inc(v___x_941_);
lean_inc_n(v_ref_953_, 2);
lean_inc_n(v_n_940_, 2);
lean_inc(v_paramInfoOverrides_955_);
lean_inc_ref(v___x_939_);
lean_inc_ref(v_a_938_);
lean_inc_ref(v_b_944_);
lean_inc_ref(v_self_937_);
lean_inc_ref(v_params_936_);
lean_inc(v___x_935_);
lean_inc(v_a_943_);
lean_inc(v___x_933_);
lean_inc_n(v_projName_954_, 2);
lean_inc_ref(v___x_932_);
v___f_959_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_959_, 0, v___x_932_);
lean_closure_set(v___f_959_, 1, v_projName_954_);
lean_closure_set(v___f_959_, 2, v___x_933_);
lean_closure_set(v___f_959_, 3, v_a_943_);
lean_closure_set(v___f_959_, 4, v___x_956_);
lean_closure_set(v___f_959_, 5, v___x_935_);
lean_closure_set(v___f_959_, 6, v_params_936_);
lean_closure_set(v___f_959_, 7, v_self_937_);
lean_closure_set(v___f_959_, 8, v_b_944_);
lean_closure_set(v___f_959_, 9, v___x_957_);
lean_closure_set(v___f_959_, 10, v_a_938_);
lean_closure_set(v___f_959_, 11, v___x_939_);
lean_closure_set(v___f_959_, 12, v_paramInfoOverrides_955_);
lean_closure_set(v___f_959_, 13, v_n_940_);
lean_closure_set(v___f_959_, 14, v_ref_953_);
lean_closure_set(v___f_959_, 15, v___x_941_);
lean_closure_set(v___f_959_, 16, v___x_958_);
v___x_960_ = l_Lean_Expr_isForall(v_b_944_);
lean_dec_ref(v_b_944_);
v___x_961_ = lean_box(v___x_960_);
v___y_962_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_962_, 0, v___x_961_);
lean_closure_set(v___y_962_, 1, v_projName_954_);
lean_closure_set(v___y_962_, 2, v_n_940_);
lean_closure_set(v___y_962_, 3, v_ref_953_);
lean_closure_set(v___y_962_, 4, v___f_959_);
v___x_963_ = l_Lean_isPrivateName(v_projName_954_);
v___x_964_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_962_, v___x_963_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_a_943_, v___x_966_);
lean_dec(v_a_943_);
v_a_943_ = v___x_967_;
v_b_944_ = v_a_965_;
goto _start;
}
else
{
lean_dec(v_a_943_);
lean_dec(v___x_941_);
lean_dec(v_n_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_a_938_);
lean_dec_ref(v_self_937_);
lean_dec_ref(v_params_936_);
lean_dec(v___x_935_);
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_969_ = _args[0];
lean_object* v_projDecls_970_ = _args[1];
lean_object* v___x_971_ = _args[2];
lean_object* v___x_972_ = _args[3];
lean_object* v_instImplicit_973_ = _args[4];
lean_object* v___x_974_ = _args[5];
lean_object* v_params_975_ = _args[6];
lean_object* v_self_976_ = _args[7];
lean_object* v_a_977_ = _args[8];
lean_object* v___x_978_ = _args[9];
lean_object* v_n_979_ = _args[10];
lean_object* v___x_980_ = _args[11];
lean_object* v_a_981_ = _args[12];
lean_object* v_a_982_ = _args[13];
lean_object* v_b_983_ = _args[14];
lean_object* v___y_984_ = _args[15];
lean_object* v___y_985_ = _args[16];
lean_object* v___y_986_ = _args[17];
lean_object* v___y_987_ = _args[18];
lean_object* v___y_988_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_989_; uint8_t v_a_17890__boxed_990_; lean_object* v_res_991_; 
v_instImplicit_boxed_989_ = lean_unbox(v_instImplicit_973_);
v_a_17890__boxed_990_ = lean_unbox(v_a_981_);
v_res_991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_969_, v_projDecls_970_, v___x_971_, v___x_972_, v_instImplicit_boxed_989_, v___x_974_, v_params_975_, v_self_976_, v_a_977_, v___x_978_, v_n_979_, v___x_980_, v_a_17890__boxed_990_, v_a_982_, v_b_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_projDecls_970_);
lean_dec(v_upperBound_969_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_992_, lean_object* v_as_993_, size_t v_sz_994_, size_t v_i_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_a_1002_; uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_995_, v_sz_994_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_b_996_);
return v___x_1007_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1008_ = lean_array_uget_borrowed(v_as_993_, v_i_995_);
v___x_1009_ = l_Lean_Expr_fvarId_x21(v_a_1008_);
lean_inc(v___x_1009_);
v___x_1010_ = l_Lean_FVarId_getDecl___redArg(v___x_1009_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___y_1013_; uint8_t v___x_1016_; uint8_t v___x_1017_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1016_ = l_Lean_LocalDecl_binderInfo(v_a_1011_);
v___x_1017_ = l_Lean_BinderInfo_isInstImplicit(v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = l_Lean_LocalDecl_type(v_a_1011_);
lean_dec(v_a_1011_);
v___x_1020_ = l_Lean_Expr_isOutParam(v___x_1019_);
lean_dec_ref(v___x_1019_);
if (v___x_1020_ == 0)
{
uint8_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = 0;
v___x_1022_ = l_Lean_LocalContext_setBinderInfo(v_b_996_, v___x_1009_, v___x_1021_);
v_a_1002_ = v___x_1022_;
goto v___jp_1001_;
}
else
{
goto v___jp_1018_;
}
}
else
{
lean_dec(v_a_1011_);
goto v___jp_1018_;
}
v___jp_1012_:
{
if (v___y_1013_ == 0)
{
lean_dec(v___x_1009_);
v_a_1002_ = v_b_996_;
goto v___jp_1001_;
}
else
{
uint8_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = 1;
v___x_1015_ = l_Lean_LocalContext_setBinderInfo(v_b_996_, v___x_1009_, v___x_1014_);
v_a_1002_ = v___x_1015_;
goto v___jp_1001_;
}
}
v___jp_1018_:
{
if (v___x_1017_ == 0)
{
v___y_1013_ = v___x_1017_;
goto v___jp_1012_;
}
else
{
v___y_1013_ = v_instImplicit_992_;
goto v___jp_1012_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v___x_1009_);
lean_dec_ref(v_b_996_);
v_a_1023_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1010_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1010_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
v___jp_1001_:
{
size_t v___x_1003_; size_t v___x_1004_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_995_, v___x_1003_);
v_i_995_ = v___x_1004_;
v_b_996_ = v_a_1002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_1031_, lean_object* v_as_1032_, lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_b_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_instImplicit_boxed_1040_; size_t v_sz_boxed_1041_; size_t v_i_boxed_1042_; lean_object* v_res_1043_; 
v_instImplicit_boxed_1040_ = lean_unbox(v_instImplicit_1031_);
v_sz_boxed_1041_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1042_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_1040_, v_as_1032_, v_sz_boxed_1041_, v_i_boxed_1042_, v_b_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_as_1032_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1044_, uint8_t v_instImplicit_1045_, lean_object* v_projDecls_1046_, lean_object* v_toConstantVal_1047_, lean_object* v_numParams_1048_, lean_object* v___x_1049_, lean_object* v_n_1050_, lean_object* v_levelParams_1051_, uint8_t v_a_1052_, lean_object* v_ctorType_1053_, lean_object* v_self_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_lctx_1060_; lean_object* v___x_1061_; size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v_lctx_1060_ = lean_ctor_get(v___y_1055_, 2);
lean_inc_ref(v_self_1054_);
lean_inc_ref(v_params_1044_);
v___x_1061_ = lean_array_push(v_params_1044_, v_self_1054_);
v_sz_1062_ = lean_array_size(v_params_1044_);
v___x_1063_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1060_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1045_, v_params_1044_, v_sz_1062_, v___x_1063_, v_lctx_1060_, v___y_1055_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = lean_array_get_size(v_projDecls_1046_);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1066_, v_projDecls_1046_, v_toConstantVal_1047_, v_numParams_1048_, v_instImplicit_1045_, v___x_1049_, v_params_1044_, v_self_1054_, v_a_1065_, v___x_1061_, v_n_1050_, v_levelParams_1051_, v_a_1052_, v___x_1067_, v_ctorType_1053_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1077_);
v___x_1070_ = v___x_1068_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1068_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1068_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1068_);
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
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_self_1054_);
lean_dec_ref(v_ctorType_1053_);
lean_dec(v_levelParams_1051_);
lean_dec(v_n_1050_);
lean_dec(v___x_1049_);
lean_dec(v_numParams_1048_);
lean_dec_ref(v_toConstantVal_1047_);
lean_dec_ref(v_params_1044_);
v_a_1086_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1064_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1064_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1094_, lean_object* v_instImplicit_1095_, lean_object* v_projDecls_1096_, lean_object* v_toConstantVal_1097_, lean_object* v_numParams_1098_, lean_object* v___x_1099_, lean_object* v_n_1100_, lean_object* v_levelParams_1101_, lean_object* v_a_1102_, lean_object* v_ctorType_1103_, lean_object* v_self_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_instImplicit_boxed_1110_; uint8_t v_a_18032__boxed_1111_; lean_object* v_res_1112_; 
v_instImplicit_boxed_1110_ = lean_unbox(v_instImplicit_1095_);
v_a_18032__boxed_1111_ = lean_unbox(v_a_1102_);
v_res_1112_ = l_Lean_Meta_mkProjections___lam__0(v_params_1094_, v_instImplicit_boxed_1110_, v_projDecls_1096_, v_toConstantVal_1097_, v_numParams_1098_, v___x_1099_, v_n_1100_, v_levelParams_1101_, v_a_18032__boxed_1111_, v_ctorType_1103_, v_self_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_projDecls_1096_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1122_, lean_object* v_projDecls_1123_, lean_object* v_toConstantVal_1124_, lean_object* v_numParams_1125_, lean_object* v___x_1126_, lean_object* v_n_1127_, lean_object* v_levelParams_1128_, uint8_t v_a_1129_, lean_object* v_params_1130_, lean_object* v_ctorType_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___y_1144_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___f_1150_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1148_ = lean_box(v_instImplicit_1122_);
v___x_1149_ = lean_box(v_a_1129_);
lean_inc(v_n_1127_);
lean_inc(v___x_1126_);
lean_inc(v_numParams_1125_);
lean_inc_ref(v_params_1130_);
v___f_1150_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1150_, 0, v_params_1130_);
lean_closure_set(v___f_1150_, 1, v___x_1148_);
lean_closure_set(v___f_1150_, 2, v_projDecls_1123_);
lean_closure_set(v___f_1150_, 3, v_toConstantVal_1124_);
lean_closure_set(v___f_1150_, 4, v_numParams_1125_);
lean_closure_set(v___f_1150_, 5, v___x_1126_);
lean_closure_set(v___f_1150_, 6, v_n_1127_);
lean_closure_set(v___f_1150_, 7, v_levelParams_1128_);
lean_closure_set(v___f_1150_, 8, v___x_1149_);
lean_closure_set(v___f_1150_, 9, v_ctorType_1131_);
v___x_1156_ = lean_array_get_size(v_params_1130_);
v___x_1157_ = lean_nat_dec_eq(v___x_1156_, v_numParams_1125_);
lean_dec(v_numParams_1125_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec_ref(v___f_1150_);
lean_dec_ref(v_params_1130_);
lean_dec(v___x_1126_);
v___x_1158_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1159_ = l_Lean_MessageData_ofConstName(v_n_1127_, v___x_1157_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1162_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1163_;
}
else
{
goto v___jp_1151_;
}
v___jp_1137_:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1146_ = 0;
v___x_1147_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1145_, v___y_1144_, v___y_1141_, v___y_1143_, v___x_1146_, v___y_1139_, v___y_1142_, v___y_1138_, v___y_1140_);
return v___x_1147_;
}
v___jp_1151_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = l_Lean_Expr_const___override(v_n_1127_, v___x_1126_);
v___x_1153_ = l_Lean_mkAppN(v___x_1152_, v_params_1130_);
lean_dec_ref(v_params_1130_);
if (v_instImplicit_1122_ == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
v___y_1138_ = v___y_1134_;
v___y_1139_ = v___y_1132_;
v___y_1140_ = v___y_1135_;
v___y_1141_ = v___x_1153_;
v___y_1142_ = v___y_1133_;
v___y_1143_ = v___f_1150_;
v___y_1144_ = v___x_1154_;
goto v___jp_1137_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = 3;
v___y_1138_ = v___y_1134_;
v___y_1139_ = v___y_1132_;
v___y_1140_ = v___y_1135_;
v___y_1141_ = v___x_1153_;
v___y_1142_ = v___y_1133_;
v___y_1143_ = v___f_1150_;
v___y_1144_ = v___x_1155_;
goto v___jp_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1164_, lean_object* v_projDecls_1165_, lean_object* v_toConstantVal_1166_, lean_object* v_numParams_1167_, lean_object* v___x_1168_, lean_object* v_n_1169_, lean_object* v_levelParams_1170_, lean_object* v_a_1171_, lean_object* v_params_1172_, lean_object* v_ctorType_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v_instImplicit_boxed_1179_; uint8_t v_a_18136__boxed_1180_; lean_object* v_res_1181_; 
v_instImplicit_boxed_1179_ = lean_unbox(v_instImplicit_1164_);
v_a_18136__boxed_1180_ = lean_unbox(v_a_1171_);
v_res_1181_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1179_, v_projDecls_1165_, v_toConstantVal_1166_, v_numParams_1167_, v___x_1168_, v_n_1169_, v_levelParams_1170_, v_a_18136__boxed_1180_, v_params_1172_, v_ctorType_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
if (lean_obj_tag(v_a_1182_) == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = l_List_reverse___redArg(v_a_1183_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
v_head_1185_ = lean_ctor_get(v_a_1182_, 0);
v_tail_1186_ = lean_ctor_get(v_a_1182_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1182_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1188_ = v_a_1182_;
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_tail_1186_);
lean_inc(v_head_1185_);
lean_dec(v_a_1182_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = l_Lean_mkLevelParam(v_head_1185_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_a_1183_);
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_a_1183_);
v___x_1192_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v_a_1182_ = v_tail_1186_;
v_a_1183_ = v___x_1192_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_instMonadEIO___redArg();
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_toApplicative_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1270_; 
v___x_1207_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
v_toApplicative_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1271_);
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1270_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_toApplicative_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1270_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_toFunctor_1213_; lean_object* v_toSeq_1214_; lean_object* v_toSeqLeft_1215_; lean_object* v_toSeqRight_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1268_; 
v_toFunctor_1213_ = lean_ctor_get(v_toApplicative_1209_, 0);
v_toSeq_1214_ = lean_ctor_get(v_toApplicative_1209_, 2);
v_toSeqLeft_1215_ = lean_ctor_get(v_toApplicative_1209_, 3);
v_toSeqRight_1216_ = lean_ctor_get(v_toApplicative_1209_, 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_toApplicative_1209_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_toApplicative_1209_, 1);
lean_dec(v_unused_1269_);
v___x_1218_ = v_toApplicative_1209_;
v_isShared_1219_ = v_isSharedCheck_1268_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_toSeqRight_1216_);
lean_inc(v_toSeqLeft_1215_);
lean_inc(v_toSeq_1214_);
lean_inc(v_toFunctor_1213_);
lean_dec(v_toApplicative_1209_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1268_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1229_; 
v___f_1220_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1221_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1213_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___f_1222_);
lean_ctor_set(v___x_1224_, 1, v___f_1223_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
v___f_1226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 4, v___f_1225_);
lean_ctor_set(v___x_1218_, 3, v___f_1226_);
lean_ctor_set(v___x_1218_, 2, v___f_1227_);
lean_ctor_set(v___x_1218_, 1, v___f_1220_);
lean_ctor_set(v___x_1218_, 0, v___x_1224_);
v___x_1229_ = v___x_1218_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___f_1220_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v___f_1227_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v___f_1226_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v___f_1225_);
v___x_1229_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___f_1221_);
lean_ctor_set(v___x_1211_, 0, v___x_1229_);
v___x_1231_ = v___x_1211_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___f_1221_);
v___x_1231_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v_toApplicative_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1264_; 
v___x_1232_ = l_StateRefT_x27_instMonad___redArg(v___x_1231_);
v_toApplicative_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1232_, 1);
lean_dec(v_unused_1265_);
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1264_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_toApplicative_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1264_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v_toFunctor_1237_; lean_object* v_toSeq_1238_; lean_object* v_toSeqLeft_1239_; lean_object* v_toSeqRight_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1262_; 
v_toFunctor_1237_ = lean_ctor_get(v_toApplicative_1233_, 0);
v_toSeq_1238_ = lean_ctor_get(v_toApplicative_1233_, 2);
v_toSeqLeft_1239_ = lean_ctor_get(v_toApplicative_1233_, 3);
v_toSeqRight_1240_ = lean_ctor_get(v_toApplicative_1233_, 4);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_toApplicative_1233_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v_toApplicative_1233_, 1);
lean_dec(v_unused_1263_);
v___x_1242_ = v_toApplicative_1233_;
v_isShared_1243_ = v_isSharedCheck_1262_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_toSeqRight_1240_);
lean_inc(v_toSeqLeft_1239_);
lean_inc(v_toSeq_1238_);
lean_inc(v_toFunctor_1237_);
lean_dec(v_toApplicative_1233_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1262_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1253_; 
v___f_1244_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1245_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1237_);
v___f_1246_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1246_, 0, v_toFunctor_1237_);
v___f_1247_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1247_, 0, v_toFunctor_1237_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___f_1246_);
lean_ctor_set(v___x_1248_, 1, v___f_1247_);
v___f_1249_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1249_, 0, v_toSeqRight_1240_);
v___f_1250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1250_, 0, v_toSeqLeft_1239_);
v___f_1251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1251_, 0, v_toSeq_1238_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___f_1249_);
lean_ctor_set(v___x_1242_, 3, v___f_1250_);
lean_ctor_set(v___x_1242_, 2, v___f_1251_);
lean_ctor_set(v___x_1242_, 1, v___f_1244_);
lean_ctor_set(v___x_1242_, 0, v___x_1248_);
v___x_1253_ = v___x_1242_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___f_1244_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v___f_1251_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v___f_1250_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v___f_1249_);
v___x_1253_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___f_1245_);
lean_ctor_set(v___x_1235_, 0, v___x_1253_);
v___x_1255_ = v___x_1235_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___f_1245_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_13115__overap_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = l_instInhabitedOfMonad___redArg(v___x_1255_, v___x_1256_);
v___x_13115__overap_1258_ = lean_panic_fn_borrowed(v___x_1257_, v_msg_1201_);
lean_dec(v___x_1257_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
v___x_1259_ = lean_apply_5(v___x_13115__overap_1258_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, lean_box(0));
return v___x_1259_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1278_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1285_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1286_ = lean_unsigned_to_nat(11u);
v___x_1287_ = lean_unsigned_to_nat(122u);
v___x_1288_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1289_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1290_ = l_mkPanicMessageWithDecl(v___x_1289_, v___x_1288_, v___x_1287_, v___x_1286_, v___x_1285_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1305_; lean_object* v_env_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_st_ref_get(v___y_1295_);
v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = 0;
lean_inc(v_constName_1291_);
v___x_1308_ = l_Lean_Environment_findAsync_x3f(v_env_1306_, v_constName_1291_, v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 1)
{
lean_object* v_val_1309_; uint8_t v_kind_1310_; 
v_val_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v_kind_1310_ = lean_ctor_get_uint8(v_val_1309_, sizeof(void*)*3);
if (v_kind_1310_ == 6)
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1309_);
if (lean_obj_tag(v___x_1311_) == 6)
{
lean_object* v_val_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_constName_1291_);
v_val_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_val_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 0);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_val_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v___x_1311_);
v___x_1320_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1321_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1320_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
if (lean_obj_tag(v_a_1322_) == 0)
{
lean_del_object(v___x_1324_);
goto v___jp_1297_;
}
else
{
lean_object* v_val_1326_; lean_object* v___x_1328_; 
lean_dec(v_constName_1291_);
v_val_1326_ = lean_ctor_get(v_a_1322_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v_a_1322_, 1);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_val_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_val_1326_);
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
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_constName_1291_);
v_a_1331_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1321_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1321_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_dec(v_val_1309_);
goto v___jp_1297_;
}
}
else
{
lean_dec(v___x_1308_);
goto v___jp_1297_;
}
v___jp_1297_:
{
lean_object* v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1298_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1299_ = 0;
v___x_1300_ = l_Lean_MessageData_ofConstName(v_constName_1291_, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1298_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1303_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1345_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v_env_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_st_ref_get(v___y_1353_);
v_env_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc_ref(v_env_1356_);
lean_dec(v___x_1355_);
lean_inc(v_constName_1349_);
v___x_1357_ = l_Lean_isInductiveCore_x3f(v_env_1356_, v_constName_1349_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1358_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1359_ = 0;
v___x_1360_ = l_Lean_MessageData_ofConstName(v_constName_1349_, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1358_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1363_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_constName_1349_);
v_val_1365_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1357_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v___x_1357_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_val_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1386_, lean_object* v___x_1387_, uint8_t v_instImplicit_1388_, lean_object* v_projDecls_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
lean_inc(v_n_1386_);
v___x_1395_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1386_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1437_ = l_Lean_InductiveVal_numCtors(v_a_1396_);
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_dec_eq(v___x_1437_, v___x_1438_);
lean_dec(v___x_1437_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v_a_1396_);
lean_dec_ref(v_projDecls_1389_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1441_ = l_Lean_MessageData_ofConstName(v_n_1386_, v___x_1439_);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1444_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
return v___x_1445_;
}
else
{
v___y_1398_ = v___y_1390_;
v___y_1399_ = v___y_1391_;
v___y_1400_ = v___y_1392_;
v___y_1401_ = v___y_1393_;
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v_toConstantVal_1402_; lean_object* v_numParams_1403_; lean_object* v_ctors_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_toConstantVal_1402_ = lean_ctor_get(v_a_1396_, 0);
lean_inc_ref(v_toConstantVal_1402_);
v_numParams_1403_ = lean_ctor_get(v_a_1396_, 1);
lean_inc(v_numParams_1403_);
v_ctors_1404_ = lean_ctor_get(v_a_1396_, 4);
lean_inc(v_ctors_1404_);
lean_dec(v_a_1396_);
v___x_1405_ = l_List_head_x21___redArg(v___x_1387_, v_ctors_1404_);
lean_dec(v_ctors_1404_);
v___x_1406_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1405_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_levelParams_1408_; lean_object* v_type_1409_; lean_object* v___x_1410_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v_levelParams_1408_ = lean_ctor_get(v_toConstantVal_1402_, 1);
lean_inc(v_levelParams_1408_);
v_type_1409_ = lean_ctor_get(v_toConstantVal_1402_, 2);
lean_inc_ref(v_type_1409_);
lean_dec_ref(v_toConstantVal_1402_);
v___x_1410_ = l_Lean_Meta_isPropFormerType(v_type_1409_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_toConstantVal_1411_; lean_object* v_a_1412_; lean_object* v_type_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v_toConstantVal_1411_ = lean_ctor_get(v_a_1407_, 0);
lean_inc_ref(v_toConstantVal_1411_);
lean_dec(v_a_1407_);
v_a_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1410_, 1);
v_type_1413_ = lean_ctor_get(v_toConstantVal_1411_, 2);
lean_inc_ref(v_type_1413_);
v___x_1414_ = lean_box(0);
lean_inc(v_levelParams_1408_);
v___x_1415_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1408_, v___x_1414_);
v___x_1416_ = lean_box(v_instImplicit_1388_);
lean_inc(v_numParams_1403_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1417_, 0, v___x_1416_);
lean_closure_set(v___f_1417_, 1, v_projDecls_1389_);
lean_closure_set(v___f_1417_, 2, v_toConstantVal_1411_);
lean_closure_set(v___f_1417_, 3, v_numParams_1403_);
lean_closure_set(v___f_1417_, 4, v___x_1415_);
lean_closure_set(v___f_1417_, 5, v_n_1386_);
lean_closure_set(v___f_1417_, 6, v_levelParams_1408_);
lean_closure_set(v___f_1417_, 7, v_a_1412_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_numParams_1403_);
v___x_1419_ = 0;
v___x_1420_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_1413_, v___x_1418_, v___f_1417_, v___x_1419_, v___x_1419_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_levelParams_1408_);
lean_dec(v_a_1407_);
lean_dec(v_numParams_1403_);
lean_dec_ref(v_projDecls_1389_);
lean_dec(v_n_1386_);
v_a_1421_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1410_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1410_);
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
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v_numParams_1403_);
lean_dec_ref(v_toConstantVal_1402_);
lean_dec_ref(v_projDecls_1389_);
lean_dec(v_n_1386_);
v_a_1429_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1406_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1406_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_projDecls_1389_);
lean_dec(v_n_1386_);
v_a_1446_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1395_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1395_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1454_, lean_object* v___x_1455_, lean_object* v_instImplicit_1456_, lean_object* v_projDecls_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_instImplicit_boxed_1463_; lean_object* v_res_1464_; 
v_instImplicit_boxed_1463_ = lean_unbox(v_instImplicit_1456_);
v_res_1464_ = l_Lean_Meta_mkProjections___lam__2(v_n_1454_, v___x_1455_, v_instImplicit_boxed_1463_, v_projDecls_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___x_1455_);
return v_res_1464_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(32u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1470_ = ((size_t)5ULL);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_unsigned_to_nat(32u);
v___x_1473_ = lean_mk_empty_array_with_capacity(v___x_1472_);
v___x_1474_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1475_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1473_);
lean_ctor_set(v___x_1475_, 2, v___x_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1471_);
lean_ctor_set_usize(v___x_1475_, 4, v___x_1470_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_box(1);
v___x_1477_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1478_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
lean_ctor_set(v___x_1479_, 2, v___x_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1482_, lean_object* v_projDecls_1483_, uint8_t v_instImplicit_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_box(v_instImplicit_1484_);
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1492_, 0, v_n_1482_);
lean_closure_set(v___f_1492_, 1, v___x_1490_);
lean_closure_set(v___f_1492_, 2, v___x_1491_);
lean_closure_set(v___f_1492_, 3, v_projDecls_1483_);
v___x_1493_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1494_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1495_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1493_, v___x_1494_, v___f_1492_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1496_, lean_object* v_projDecls_1497_, lean_object* v_instImplicit_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
uint8_t v_instImplicit_boxed_1504_; lean_object* v_res_1505_; 
v_instImplicit_boxed_1504_ = lean_unbox(v_instImplicit_1498_);
v_res_1505_ = l_Lean_Meta_mkProjections(v_n_1496_, v_projDecls_1497_, v_instImplicit_boxed_1504_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1506_, lean_object* v_as_1507_, size_t v_sz_1508_, size_t v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1506_, v_as_1507_, v_sz_1508_, v_i_1509_, v_b_1510_, v___y_1511_, v___y_1513_, v___y_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1517_, lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_instImplicit_boxed_1527_; size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_instImplicit_boxed_1527_ = lean_unbox(v_instImplicit_1517_);
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1527_, v_as_1518_, v_sz_boxed_1528_, v_i_boxed_1529_, v_b_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec_ref(v_as_1518_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1531_, uint8_t v_s_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1531_, v_s_1532_, v___y_1534_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1539_, lean_object* v_s_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v_s_boxed_1546_; lean_object* v_res_1547_; 
v_s_boxed_1546_ = lean_unbox(v_s_1540_);
v_res_1547_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1539_, v_s_boxed_1546_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1548_, lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1557_, lean_object* v_ref_1558_, lean_object* v_msg_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1557_, v_ref_1558_, v_msg_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_ref_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1566_, lean_object* v_x_1567_, uint8_t v_isExporting_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1567_, v_isExporting_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_x_1576_, lean_object* v_isExporting_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
uint8_t v_isExporting_boxed_1583_; lean_object* v_res_1584_; 
v_isExporting_boxed_1583_ = lean_unbox(v_isExporting_1577_);
v_res_1584_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1575_, v_x_1576_, v_isExporting_boxed_1583_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1585_, lean_object* v_x_1586_, uint8_t v_when_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1586_, v_when_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_x_1595_, lean_object* v_when_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_when_boxed_1602_; lean_object* v_res_1603_; 
v_when_boxed_1602_ = lean_unbox(v_when_1596_);
v_res_1603_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1594_, v_x_1595_, v_when_boxed_1602_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1604_, lean_object* v_projDecls_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, uint8_t v_instImplicit_1608_, lean_object* v___x_1609_, lean_object* v_params_1610_, lean_object* v_self_1611_, lean_object* v_a_1612_, lean_object* v___x_1613_, lean_object* v_n_1614_, lean_object* v___x_1615_, uint8_t v_a_1616_, lean_object* v_inst_1617_, lean_object* v_R_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v_c_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1604_, v_projDecls_1605_, v___x_1606_, v___x_1607_, v_instImplicit_1608_, v___x_1609_, v_params_1610_, v_self_1611_, v_a_1612_, v___x_1613_, v_n_1614_, v___x_1615_, v_a_1616_, v_a_1619_, v_b_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1628_ = _args[0];
lean_object* v_projDecls_1629_ = _args[1];
lean_object* v___x_1630_ = _args[2];
lean_object* v___x_1631_ = _args[3];
lean_object* v_instImplicit_1632_ = _args[4];
lean_object* v___x_1633_ = _args[5];
lean_object* v_params_1634_ = _args[6];
lean_object* v_self_1635_ = _args[7];
lean_object* v_a_1636_ = _args[8];
lean_object* v___x_1637_ = _args[9];
lean_object* v_n_1638_ = _args[10];
lean_object* v___x_1639_ = _args[11];
lean_object* v_a_1640_ = _args[12];
lean_object* v_inst_1641_ = _args[13];
lean_object* v_R_1642_ = _args[14];
lean_object* v_a_1643_ = _args[15];
lean_object* v_b_1644_ = _args[16];
lean_object* v_c_1645_ = _args[17];
lean_object* v___y_1646_ = _args[18];
lean_object* v___y_1647_ = _args[19];
lean_object* v___y_1648_ = _args[20];
lean_object* v___y_1649_ = _args[21];
lean_object* v___y_1650_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1651_; uint8_t v_a_18887__boxed_1652_; lean_object* v_res_1653_; 
v_instImplicit_boxed_1651_ = lean_unbox(v_instImplicit_1632_);
v_a_18887__boxed_1652_ = lean_unbox(v_a_1640_);
v_res_1653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1628_, v_projDecls_1629_, v___x_1630_, v___x_1631_, v_instImplicit_boxed_1651_, v___x_1633_, v_params_1634_, v_self_1635_, v_a_1636_, v___x_1637_, v_n_1638_, v___x_1639_, v_a_18887__boxed_1652_, v_inst_1641_, v_R_1642_, v_a_1643_, v_b_1644_, v_c_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_projDecls_1629_);
lean_dec(v_upperBound_1628_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1654_, uint8_t v_allowLevelAssignments_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1655_, v_k_1654_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1661_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1661_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1678_, lean_object* v_allowLevelAssignments_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1685_; lean_object* v_res_1686_; 
v_allowLevelAssignments_boxed_1685_ = lean_unbox(v_allowLevelAssignments_1679_);
v_res_1686_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1678_, v_allowLevelAssignments_boxed_1685_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1687_, lean_object* v_k_1688_, uint8_t v_allowLevelAssignments_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1688_, v_allowLevelAssignments_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_k_1697_, lean_object* v_allowLevelAssignments_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1704_; lean_object* v_res_1705_; 
v_allowLevelAssignments_boxed_1704_ = lean_unbox(v_allowLevelAssignments_1698_);
v_res_1705_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1696_, v_k_1697_, v_allowLevelAssignments_boxed_1704_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1706_, size_t v_sz_1707_, size_t v_i_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_b_1709_);
return v___x_1716_;
}
else
{
lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1772_; 
v_snd_1717_ = lean_ctor_get(v_b_1709_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_b_1709_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v_b_1709_, 0);
lean_dec(v_unused_1773_);
v___x_1719_ = v_b_1709_;
v_isShared_1720_ = v_isSharedCheck_1772_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_dec(v_b_1709_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1772_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_array_1721_; lean_object* v_start_1722_; lean_object* v_stop_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_array_1721_ = lean_ctor_get(v_snd_1717_, 0);
v_start_1722_ = lean_ctor_get(v_snd_1717_, 1);
v_stop_1723_ = lean_ctor_get(v_snd_1717_, 2);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_nat_dec_lt(v_start_1722_, v_stop_1723_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1727_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1727_ = v___x_1719_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_snd_1717_);
v___x_1727_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
else
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1768_; 
lean_inc(v_stop_1723_);
lean_inc(v_start_1722_);
lean_inc_ref(v_array_1721_);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_snd_1717_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; lean_object* v_unused_1770_; lean_object* v_unused_1771_; 
v_unused_1769_ = lean_ctor_get(v_snd_1717_, 2);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_snd_1717_, 1);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_snd_1717_, 0);
lean_dec(v_unused_1771_);
v___x_1731_ = v_snd_1717_;
v_isShared_1732_ = v_isSharedCheck_1768_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v_snd_1717_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1768_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_a_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v_a_1733_ = lean_array_uget_borrowed(v_as_1706_, v_i_1708_);
v___x_1734_ = lean_array_fget(v_array_1721_, v_start_1722_);
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_nat_add(v_start_1722_, v___x_1735_);
lean_dec(v_start_1722_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_array_1721_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_stop_1723_);
v___x_1738_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; 
lean_inc(v_a_1733_);
v___x_1739_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1733_, v___x_1734_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1758_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_unbox(v_a_1740_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_a_1740_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1738_);
lean_ctor_set(v___x_1719_, 0, v___x_1745_);
v___x_1747_ = v___x_1719_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1738_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1747_);
v___x_1749_ = v___x_1742_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v___x_1753_; 
lean_del_object(v___x_1742_);
lean_dec(v_a_1740_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1738_);
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1753_ = v___x_1719_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1738_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
size_t v___x_1754_; size_t v___x_1755_; 
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_add(v_i_1708_, v___x_1754_);
v_i_1708_ = v___x_1755_;
v_b_1709_ = v___x_1753_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v___x_1738_);
lean_del_object(v___x_1719_);
v_a_1759_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1739_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1739_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1774_, lean_object* v_sz_1775_, lean_object* v_i_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1775_);
lean_dec(v_sz_1775_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1774_, v_sz_boxed_1783_, v_i_boxed_1784_, v_b_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_as_1774_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1786_, lean_object* v_params2_1787_, lean_object* v___x_1788_, lean_object* v_params1_1789_, uint8_t v___x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
if (v___x_1786_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___x_1788_);
lean_dec_ref(v_params2_1787_);
v___x_1796_ = lean_box(v___x_1786_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; size_t v_sz_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = l_Array_toSubarray___redArg(v_params2_1787_, v___x_1798_, v___x_1788_);
v___x_1800_ = lean_box(0);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
v_sz_1802_ = lean_array_size(v_params1_1789_);
v___x_1803_ = ((size_t)0ULL);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1789_, v_sz_1802_, v___x_1803_, v___x_1801_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1818_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1818_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_fst_1809_; 
v_fst_1809_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_fst_1809_);
lean_dec(v_a_1805_);
if (lean_obj_tag(v_fst_1809_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_box(v___x_1790_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
else
{
lean_object* v_val_1814_; lean_object* v___x_1816_; 
v_val_1814_ = lean_ctor_get(v_fst_1809_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v_fst_1809_, 1);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_val_1814_);
v___x_1816_ = v___x_1807_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_val_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_a_1819_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1804_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1804_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1827_, lean_object* v_params2_1828_, lean_object* v___x_1829_, lean_object* v_params1_1830_, lean_object* v___x_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
uint8_t v___x_2007__boxed_1837_; uint8_t v___x_2009__boxed_1838_; lean_object* v_res_1839_; 
v___x_2007__boxed_1837_ = lean_unbox(v___x_1827_);
v___x_2009__boxed_1838_ = lean_unbox(v___x_1831_);
v_res_1839_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1837_, v_params2_1828_, v___x_1829_, v_params1_1830_, v___x_2009__boxed_1838_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_params1_1830_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1840_, lean_object* v_params2_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___y_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1847_ = lean_array_get_size(v_params1_1840_);
v___x_1848_ = lean_array_get_size(v_params2_1841_);
v___x_1849_ = lean_nat_dec_eq(v___x_1847_, v___x_1848_);
v___x_1850_ = 1;
v___x_1851_ = lean_box(v___x_1849_);
v___x_1852_ = lean_box(v___x_1850_);
v___y_1853_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1853_, 0, v___x_1851_);
lean_closure_set(v___y_1853_, 1, v_params2_1841_);
lean_closure_set(v___y_1853_, 2, v___x_1848_);
lean_closure_set(v___y_1853_, 3, v_params1_1840_);
lean_closure_set(v___y_1853_, 4, v___x_1852_);
v___x_1854_ = 0;
v___x_1855_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1853_, v___x_1854_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1856_, lean_object* v_params2_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1856_, v_params2_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_env_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = lean_st_ref_get(v___y_1865_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1868_);
lean_dec(v___x_1867_);
v___x_1869_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1868_, v_declName_1864_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1871_, v___y_1872_);
lean_dec(v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1875_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1889_; lean_object* v_dummy_1890_; 
v___x_1889_ = lean_box(0);
v_dummy_1890_ = l_Lean_Expr_sort___override(v___x_1889_);
return v_dummy_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1891_, lean_object* v_induct_1892_, lean_object* v_params_1893_, lean_object* v_idx_1894_, lean_object* v_e_1895_, lean_object* v_x_x3f_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
if (lean_obj_tag(v_e_1895_) == 11)
{
lean_object* v_typeName_1908_; lean_object* v_idx_1909_; lean_object* v_struct_1910_; uint8_t v___x_1957_; 
v_typeName_1908_ = lean_ctor_get(v_e_1895_, 0);
v_idx_1909_ = lean_ctor_get(v_e_1895_, 1);
v_struct_1910_ = lean_ctor_get(v_e_1895_, 2);
lean_inc_ref(v_struct_1910_);
v___x_1957_ = lean_nat_dec_eq(v_idx_1909_, v_idx_1894_);
if (v___x_1957_ == 0)
{
lean_dec_ref(v_struct_1910_);
lean_dec_ref_known(v_e_1895_, 3);
lean_dec_ref(v_params_1893_);
goto v___jp_1902_;
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_name_eq(v_induct_1892_, v_typeName_1908_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_struct_1910_);
lean_dec_ref_known(v_e_1895_, 3);
lean_dec_ref(v_params_1893_);
goto v___jp_1902_;
}
else
{
if (lean_obj_tag(v_x_x3f_1896_) == 0)
{
goto v___jp_1911_;
}
else
{
lean_object* v_val_1959_; uint8_t v___x_1960_; 
v_val_1959_ = lean_ctor_get(v_x_x3f_1896_, 0);
v___x_1960_ = lean_expr_eqv(v_val_1959_, v_struct_1910_);
if (v___x_1960_ == 0)
{
lean_dec_ref(v_struct_1910_);
lean_dec_ref_known(v_e_1895_, 3);
lean_dec_ref(v_params_1893_);
goto v___jp_1902_;
}
else
{
goto v___jp_1911_;
}
}
}
}
v___jp_1911_:
{
lean_object* v___x_1912_; 
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
v___x_1912_ = lean_infer_type(v_e_1895_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
v___x_1914_ = lean_whnf(v_a_1913_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_dummy_1916_; lean_object* v_nargs_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v_dummy_1916_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1917_ = l_Lean_Expr_getAppNumArgs(v_a_1915_);
lean_inc(v_nargs_1917_);
v___x_1918_ = lean_mk_array(v_nargs_1917_, v_dummy_1916_);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_sub(v_nargs_1917_, v___x_1919_);
lean_dec(v_nargs_1917_);
v___x_1921_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1915_, v___x_1918_, v___x_1920_);
v___x_1922_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1893_, v___x_1921_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1932_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_unbox(v_a_1923_);
lean_dec(v_a_1923_);
if (v___x_1927_ == 0)
{
lean_del_object(v___x_1925_);
lean_dec_ref(v_struct_1910_);
goto v___jp_1902_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_struct_1910_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1928_);
v___x_1930_ = v___x_1925_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_struct_1910_);
v_a_1933_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1922_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1922_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_struct_1910_);
lean_dec_ref(v_params_1893_);
v_a_1941_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1914_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1914_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_struct_1910_);
lean_dec_ref(v_params_1893_);
v_a_1949_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1912_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1912_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Expr_getAppFn(v_e_1895_);
if (lean_obj_tag(v___x_1961_) == 4)
{
lean_object* v_declName_1962_; lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2013_; 
v_declName_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_declName_1962_);
lean_dec_ref_known(v___x_1961_, 2);
v___x_1963_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1962_, v_a_1900_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_2013_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2013_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___y_1969_; lean_object* v___y_1970_; 
if (lean_obj_tag(v_a_1964_) == 1)
{
lean_object* v_val_1998_; lean_object* v_ctorName_1999_; lean_object* v_numParams_2000_; lean_object* v_i_2001_; uint8_t v___y_2003_; uint8_t v___x_2011_; 
v_val_1998_ = lean_ctor_get(v_a_1964_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_a_1964_, 1);
v_ctorName_1999_ = lean_ctor_get(v_val_1998_, 0);
lean_inc(v_ctorName_1999_);
v_numParams_2000_ = lean_ctor_get(v_val_1998_, 1);
lean_inc(v_numParams_2000_);
v_i_2001_ = lean_ctor_get(v_val_1998_, 2);
lean_inc(v_i_2001_);
lean_dec(v_val_1998_);
v___x_2011_ = lean_name_eq(v_ctorName_1999_, v_ctor_1891_);
lean_dec(v_ctorName_1999_);
if (v___x_2011_ == 0)
{
lean_dec(v_i_2001_);
v___y_2003_ = v___x_2011_;
goto v___jp_2002_;
}
else
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_nat_dec_eq(v_i_2001_, v_idx_1894_);
lean_dec(v_i_2001_);
v___y_2003_ = v___x_2012_;
goto v___jp_2002_;
}
v___jp_2002_:
{
if (v___y_2003_ == 0)
{
lean_dec(v_numParams_2000_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_params_1893_);
goto v___jp_1905_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2004_ = l_Lean_Expr_getAppNumArgs(v_e_1895_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_add(v_numParams_2000_, v___x_2005_);
lean_dec(v_numParams_2000_);
v___x_2007_ = lean_nat_dec_eq(v___x_2004_, v___x_2006_);
lean_dec(v___x_2006_);
lean_dec(v___x_2004_);
if (v___x_2007_ == 0)
{
lean_del_object(v___x_1966_);
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_params_1893_);
goto v___jp_1905_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Expr_appArg_x21(v_e_1895_);
if (lean_obj_tag(v_x_x3f_1896_) == 0)
{
v___y_1969_ = v___x_2005_;
v___y_1970_ = v___x_2008_;
goto v___jp_1968_;
}
else
{
lean_object* v_val_2009_; uint8_t v___x_2010_; 
v_val_2009_ = lean_ctor_get(v_x_x3f_1896_, 0);
v___x_2010_ = lean_expr_eqv(v_val_2009_, v___x_2008_);
if (v___x_2010_ == 0)
{
lean_dec_ref(v___x_2008_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_params_1893_);
goto v___jp_1905_;
}
else
{
v___y_1969_ = v___x_2005_;
v___y_1970_ = v___x_2008_;
goto v___jp_1968_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1966_);
lean_dec(v_a_1964_);
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_params_1893_);
goto v___jp_1905_;
}
v___jp_1968_:
{
lean_object* v___x_1971_; lean_object* v_dummy_1972_; lean_object* v_nargs_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1971_ = l_Lean_Expr_appFn_x21(v_e_1895_);
lean_dec_ref(v_e_1895_);
v_dummy_1972_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1973_ = l_Lean_Expr_getAppNumArgs(v___x_1971_);
lean_inc(v_nargs_1973_);
v___x_1974_ = lean_mk_array(v_nargs_1973_, v_dummy_1972_);
v___x_1975_ = lean_nat_sub(v_nargs_1973_, v___y_1969_);
lean_dec(v_nargs_1973_);
v___x_1976_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1971_, v___x_1974_, v___x_1975_);
v___x_1977_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1893_, v___x_1976_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1989_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_1982_ == 0)
{
lean_del_object(v___x_1980_);
lean_dec_ref(v___y_1970_);
lean_del_object(v___x_1966_);
goto v___jp_1905_;
}
else
{
lean_object* v___x_1984_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v___y_1970_);
v___x_1984_ = v___x_1966_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___y_1970_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1984_);
v___x_1986_ = v___x_1980_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v___y_1970_);
lean_del_object(v___x_1966_);
v_a_1990_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1977_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1977_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_e_1895_);
lean_dec_ref(v_params_1893_);
goto v___jp_1905_;
}
}
v___jp_1902_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
v___jp_1905_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2014_, lean_object* v_induct_2015_, lean_object* v_params_2016_, lean_object* v_idx_2017_, lean_object* v_e_2018_, lean_object* v_x_x3f_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2014_, v_induct_2015_, v_params_2016_, v_idx_2017_, v_e_2018_, v_x_x3f_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_x_x3f_2019_);
lean_dec(v_idx_2017_);
lean_dec(v_induct_2015_);
lean_dec(v_ctor_2014_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v_env_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2032_ = lean_st_ref_get(v___y_2030_);
v_env_2036_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_ref(v_env_2036_);
lean_dec(v___x_2032_);
v___x_2037_ = 0;
v___x_2038_ = l_Lean_Environment_findAsync_x3f(v_env_2036_, v_constName_2026_, v___x_2037_);
if (lean_obj_tag(v___x_2038_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2058_; 
v_val_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2058_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2058_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v_kind_2043_; 
v_kind_2043_ = lean_ctor_get_uint8(v_val_2039_, sizeof(void*)*3);
if (v_kind_2043_ == 6)
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2039_);
if (lean_obj_tag(v___x_2044_) == 6)
{
lean_object* v_val_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
v_val_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_val_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_val_2045_);
v___x_2050_ = v___x_2041_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_val_2045_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set_tag(v___x_2047_, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2050_);
v___x_2052_ = v___x_2047_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v___x_2044_);
lean_del_object(v___x_2041_);
v___x_2056_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2057_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2056_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
return v___x_2057_;
}
}
else
{
lean_del_object(v___x_2041_);
lean_dec(v_val_2039_);
goto v___jp_2033_;
}
}
}
else
{
lean_dec(v___x_2038_);
goto v___jp_2033_;
}
v___jp_2033_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_box(0);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2074_, lean_object* v___x_2075_, lean_object* v___x_2076_, lean_object* v_declName_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, lean_object* v_a_2080_, lean_object* v_val_2081_, lean_object* v_a_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_nat_dec_lt(v_a_2082_, v_upperBound_2074_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2079_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2083_);
return v___x_2090_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v_b_2083_);
v___x_2091_ = l_Lean_instInhabitedExpr;
v___x_2092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2093_ = lean_nat_add(v___x_2075_, v_a_2082_);
v___x_2094_ = lean_array_get_borrowed(v___x_2091_, v___x_2076_, v___x_2093_);
lean_dec(v___x_2093_);
lean_inc(v___x_2094_);
lean_inc_ref(v___x_2079_);
v___x_2095_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2077_, v___x_2078_, v___x_2079_, v_a_2082_, v___x_2094_, v_a_2080_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2113_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2113_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2113_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
if (lean_obj_tag(v_a_2096_) == 1)
{
lean_object* v_val_2100_; uint8_t v___x_2101_; 
v_val_2100_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_val_2100_);
lean_dec_ref_known(v_a_2096_, 1);
v___x_2101_ = lean_expr_eqv(v_val_2100_, v_val_2081_);
lean_dec(v_val_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2079_);
v___x_2102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2102_);
v___x_2104_ = v___x_2098_;
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
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_del_object(v___x_2098_);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_add(v_a_2082_, v___x_2106_);
lean_dec(v_a_2082_);
v_a_2082_ = v___x_2107_;
v_b_2083_ = v___x_2092_;
goto _start;
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
lean_dec(v_a_2096_);
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2079_);
v___x_2109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2109_);
v___x_2111_ = v___x_2098_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2079_);
v_a_2114_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2095_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2095_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2122_, lean_object* v___x_2123_, lean_object* v___x_2124_, lean_object* v_declName_2125_, lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_a_2128_, lean_object* v_val_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2122_, v___x_2123_, v___x_2124_, v_declName_2125_, v___x_2126_, v___x_2127_, v_a_2128_, v_val_2129_, v_a_2130_, v_b_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec_ref(v_val_2129_);
lean_dec(v_a_2128_);
lean_dec(v___x_2126_);
lean_dec(v_declName_2125_);
lean_dec_ref(v___x_2124_);
lean_dec(v___x_2123_);
lean_dec(v_upperBound_2122_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2138_, lean_object* v_p_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Expr_getAppFn(v_e_2138_);
if (lean_obj_tag(v___x_2145_) == 4)
{
lean_object* v_declName_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_declName_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_n(v_declName_2146_, 2);
lean_dec_ref_known(v___x_2145_, 2);
v___x_2147_ = l_Lean_instInhabitedExpr;
v___x_2148_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2146_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2220_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2220_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2220_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
if (lean_obj_tag(v_a_2149_) == 1)
{
lean_object* v_val_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2217_; 
v_val_2158_ = lean_ctor_get(v_a_2149_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2160_ = v_a_2149_;
v_isShared_2161_ = v_isSharedCheck_2217_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_val_2158_);
lean_dec(v_a_2149_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2217_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_induct_2162_; lean_object* v_numParams_2163_; lean_object* v_numFields_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_induct_2162_ = lean_ctor_get(v_val_2158_, 1);
lean_inc_n(v_induct_2162_, 2);
v_numParams_2163_ = lean_ctor_get(v_val_2158_, 3);
lean_inc(v_numParams_2163_);
v_numFields_2164_ = lean_ctor_get(v_val_2158_, 4);
lean_inc(v_numFields_2164_);
lean_dec(v_val_2158_);
v___x_2165_ = lean_apply_1(v_p_2139_, v_induct_2162_);
v___x_2166_ = lean_unbox(v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec(v_numFields_2164_);
lean_dec(v_numParams_2163_);
lean_dec(v_induct_2162_);
lean_del_object(v___x_2151_);
lean_dec(v_declName_2146_);
lean_dec_ref(v_e_2138_);
v___x_2167_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2167_);
v___x_2169_ = v___x_2160_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
lean_del_object(v___x_2160_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_nat_dec_lt(v___x_2171_, v_numFields_2164_);
if (v___x_2172_ == 0)
{
lean_dec(v_numFields_2164_);
lean_dec(v_numParams_2163_);
lean_dec(v_induct_2162_);
lean_dec(v_declName_2146_);
lean_dec_ref(v_e_2138_);
goto v___jp_2153_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2173_ = l_Lean_Expr_getAppNumArgs(v_e_2138_);
v___x_2174_ = lean_nat_add(v_numParams_2163_, v_numFields_2164_);
v___x_2175_ = lean_nat_dec_eq(v___x_2173_, v___x_2174_);
lean_dec(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec(v___x_2173_);
lean_dec(v_numFields_2164_);
lean_dec(v_numParams_2163_);
lean_dec(v_induct_2162_);
lean_dec(v_declName_2146_);
lean_dec_ref(v_e_2138_);
goto v___jp_2153_;
}
else
{
lean_object* v_dummy_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2151_);
v_dummy_2176_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2173_);
v___x_2177_ = lean_mk_array(v___x_2173_, v_dummy_2176_);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_sub(v___x_2173_, v___x_2178_);
lean_dec(v___x_2173_);
v___x_2180_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2138_, v___x_2177_, v___x_2179_);
lean_inc(v_numParams_2163_);
v___x_2181_ = l_Array_extract___redArg(v___x_2180_, v___x_2171_, v_numParams_2163_);
v___x_2182_ = lean_array_get_borrowed(v___x_2147_, v___x_2180_, v_numParams_2163_);
v___x_2183_ = lean_box(0);
lean_inc(v___x_2182_);
lean_inc_ref(v___x_2181_);
v___x_2184_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2146_, v_induct_2162_, v___x_2181_, v___x_2171_, v___x_2182_, v___x_2183_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2216_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2216_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2216_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
if (lean_obj_tag(v_a_2185_) == 1)
{
lean_object* v_val_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_del_object(v___x_2187_);
v_val_2189_ = lean_ctor_get(v_a_2185_, 0);
v___x_2190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2164_, v_numParams_2163_, v___x_2180_, v_declName_2146_, v_induct_2162_, v___x_2181_, v_a_2185_, v_val_2189_, v___x_2178_, v___x_2190_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_induct_2162_);
lean_dec(v_declName_2146_);
lean_dec_ref(v___x_2180_);
lean_dec(v_numParams_2163_);
lean_dec(v_numFields_2164_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_fst_2196_; 
v_fst_2196_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_fst_2196_);
lean_dec(v_a_2192_);
if (lean_obj_tag(v_fst_2196_) == 0)
{
lean_object* v___x_2198_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_a_2185_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2185_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2202_; 
lean_dec_ref_known(v_a_2185_, 1);
v_val_2200_ = lean_ctor_get(v_fst_2196_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_fst_2196_, 1);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v_val_2200_);
v___x_2202_ = v___x_2194_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_val_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref_known(v_a_2185_, 1);
v_a_2205_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2191_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2191_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v___x_2214_; 
lean_dec(v_a_2185_);
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2180_);
lean_dec(v_numFields_2164_);
lean_dec(v_numParams_2163_);
lean_dec(v_induct_2162_);
lean_dec(v_declName_2146_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2183_);
v___x_2214_ = v___x_2187_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2183_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_dec_ref(v___x_2181_);
lean_dec_ref(v___x_2180_);
lean_dec(v_numFields_2164_);
lean_dec(v_numParams_2163_);
lean_dec(v_induct_2162_);
lean_dec(v_declName_2146_);
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_del_object(v___x_2151_);
lean_dec(v_a_2149_);
lean_dec(v_declName_2146_);
lean_dec_ref(v_p_2139_);
lean_dec_ref(v_e_2138_);
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
v___jp_2153_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2154_);
v___x_2156_ = v___x_2151_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_declName_2146_);
lean_dec_ref(v_p_2139_);
lean_dec_ref(v_e_2138_);
v_a_2221_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2148_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2148_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec_ref(v___x_2145_);
lean_dec_ref(v_p_2139_);
lean_dec_ref(v_e_2138_);
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2231_, lean_object* v_p_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_etaStruct_x3f(v_e_2231_, v_p_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_declName_2242_, lean_object* v___x_2243_, lean_object* v___x_2244_, lean_object* v_a_2245_, lean_object* v_val_2246_, lean_object* v_inst_2247_, lean_object* v_R_2248_, lean_object* v_a_2249_, lean_object* v_b_2250_, lean_object* v_c_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2239_, v___x_2240_, v___x_2241_, v_declName_2242_, v___x_2243_, v___x_2244_, v_a_2245_, v_val_2246_, v_a_2249_, v_b_2250_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2258_ = _args[0];
lean_object* v___x_2259_ = _args[1];
lean_object* v___x_2260_ = _args[2];
lean_object* v_declName_2261_ = _args[3];
lean_object* v___x_2262_ = _args[4];
lean_object* v___x_2263_ = _args[5];
lean_object* v_a_2264_ = _args[6];
lean_object* v_val_2265_ = _args[7];
lean_object* v_inst_2266_ = _args[8];
lean_object* v_R_2267_ = _args[9];
lean_object* v_a_2268_ = _args[10];
lean_object* v_b_2269_ = _args[11];
lean_object* v_c_2270_ = _args[12];
lean_object* v___y_2271_ = _args[13];
lean_object* v___y_2272_ = _args[14];
lean_object* v___y_2273_ = _args[15];
lean_object* v___y_2274_ = _args[16];
lean_object* v___y_2275_ = _args[17];
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2258_, v___x_2259_, v___x_2260_, v_declName_2261_, v___x_2262_, v___x_2263_, v_a_2264_, v_val_2265_, v_inst_2266_, v_R_2267_, v_a_2268_, v_b_2269_, v_c_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_val_2265_);
lean_dec(v_a_2264_);
lean_dec(v___x_2262_);
lean_dec(v_declName_2261_);
lean_dec_ref(v___x_2260_);
lean_dec(v___x_2259_);
lean_dec(v_upperBound_2258_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = l_Lean_Expr_hasMVar(v_e_2277_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_e_2277_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; lean_object* v_mctx_2283_; lean_object* v___x_2284_; lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2287_; lean_object* v_cache_2288_; lean_object* v_zetaDeltaFVarIds_2289_; lean_object* v_postponed_2290_; lean_object* v_diag_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
v___x_2282_ = lean_st_ref_get(v___y_2278_);
v_mctx_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_mctx_2283_);
lean_dec(v___x_2282_);
v___x_2284_ = l_Lean_instantiateMVarsCore(v_mctx_2283_, v_e_2277_);
v_fst_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_fst_2285_);
v_snd_2286_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2286_);
lean_dec_ref(v___x_2284_);
v___x_2287_ = lean_st_ref_take(v___y_2278_);
v_cache_2288_ = lean_ctor_get(v___x_2287_, 1);
v_zetaDeltaFVarIds_2289_ = lean_ctor_get(v___x_2287_, 2);
v_postponed_2290_ = lean_ctor_get(v___x_2287_, 3);
v_diag_2291_ = lean_ctor_get(v___x_2287_, 4);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v___x_2287_, 0);
lean_dec(v_unused_2301_);
v___x_2293_ = v___x_2287_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_diag_2291_);
lean_inc(v_postponed_2290_);
lean_inc(v_zetaDeltaFVarIds_2289_);
lean_inc(v_cache_2288_);
lean_dec(v___x_2287_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v_snd_2286_);
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_snd_2286_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_cache_2288_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_zetaDeltaFVarIds_2289_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_postponed_2290_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_diag_2291_);
v___x_2296_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_st_ref_put(v___y_2278_, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_fst_2285_);
return v___x_2298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2302_, v___y_2303_);
lean_dec(v___y_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2306_, v___y_2308_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_x_2330_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2337_, lean_object* v_e_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Meta_etaStruct_x3f(v_e_2338_, v_p_2337_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2364_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2364_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2364_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
if (lean_obj_tag(v_a_2345_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2359_; 
v_val_2349_ = lean_ctor_get(v_a_2345_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2351_ = v_a_2345_;
v_isShared_2352_ = v_isSharedCheck_2359_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_val_2349_);
lean_dec(v_a_2345_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2359_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 0);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_val_2349_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2354_);
v___x_2356_ = v___x_2347_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec(v_a_2345_);
v___x_2360_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2360_);
v___x_2362_ = v___x_2347_;
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
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2365_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2344_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2344_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2373_, lean_object* v_e_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2373_, v_e_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2381_, lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_apply_1(v_x_2382_, lean_box(0));
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2390_, v_x_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2398_, lean_object* v_b_2399_, lean_object* v_x_2400_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 0)
{
lean_dec(v_b_2399_);
lean_dec_ref(v_a_2398_);
return v_x_2400_;
}
else
{
lean_object* v_key_2401_; lean_object* v_value_2402_; lean_object* v_tail_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2415_; 
v_key_2401_ = lean_ctor_get(v_x_2400_, 0);
v_value_2402_ = lean_ctor_get(v_x_2400_, 1);
v_tail_2403_ = lean_ctor_get(v_x_2400_, 2);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_x_2400_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2405_ = v_x_2400_;
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_tail_2403_);
lean_inc(v_value_2402_);
lean_inc(v_key_2401_);
lean_dec(v_x_2400_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_ExprStructEq_beq(v_key_2401_, v_a_2398_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2398_, v_b_2399_, v_tail_2403_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 2, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_key_2401_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_value_2402_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
else
{
lean_object* v___x_2413_; 
lean_dec(v_value_2402_);
lean_dec(v_key_2401_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 1, v_b_2399_);
lean_ctor_set(v___x_2405_, 0, v_a_2398_);
v___x_2413_ = v___x_2405_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2398_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_b_2399_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_tail_2403_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
if (lean_obj_tag(v_x_2417_) == 0)
{
return v_x_2416_;
}
else
{
lean_object* v_key_2418_; lean_object* v_value_2419_; lean_object* v_tail_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2443_; 
v_key_2418_ = lean_ctor_get(v_x_2417_, 0);
v_value_2419_ = lean_ctor_get(v_x_2417_, 1);
v_tail_2420_ = lean_ctor_get(v_x_2417_, 2);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2417_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2422_ = v_x_2417_;
v_isShared_2423_ = v_isSharedCheck_2443_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_tail_2420_);
lean_inc(v_value_2419_);
lean_inc(v_key_2418_);
lean_dec(v_x_2417_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2443_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; uint64_t v___x_2425_; uint64_t v___x_2426_; uint64_t v___x_2427_; uint64_t v_fold_2428_; uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; size_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2424_ = lean_array_get_size(v_x_2416_);
v___x_2425_ = l_Lean_ExprStructEq_hash(v_key_2418_);
v___x_2426_ = 32ULL;
v___x_2427_ = lean_uint64_shift_right(v___x_2425_, v___x_2426_);
v_fold_2428_ = lean_uint64_xor(v___x_2425_, v___x_2427_);
v___x_2429_ = 16ULL;
v___x_2430_ = lean_uint64_shift_right(v_fold_2428_, v___x_2429_);
v___x_2431_ = lean_uint64_xor(v_fold_2428_, v___x_2430_);
v___x_2432_ = lean_uint64_to_usize(v___x_2431_);
v___x_2433_ = lean_usize_of_nat(v___x_2424_);
v___x_2434_ = ((size_t)1ULL);
v___x_2435_ = lean_usize_sub(v___x_2433_, v___x_2434_);
v___x_2436_ = lean_usize_land(v___x_2432_, v___x_2435_);
v___x_2437_ = lean_array_uget_borrowed(v_x_2416_, v___x_2436_);
lean_inc(v___x_2437_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 2, v___x_2437_);
v___x_2439_ = v___x_2422_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_key_2418_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_value_2419_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_array_uset(v_x_2416_, v___x_2436_, v___x_2439_);
v_x_2416_ = v___x_2440_;
v_x_2417_ = v_tail_2420_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2444_, lean_object* v_source_2445_, lean_object* v_target_2446_){
_start:
{
lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2447_ = lean_array_get_size(v_source_2445_);
v___x_2448_ = lean_nat_dec_lt(v_i_2444_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_dec_ref(v_source_2445_);
lean_dec(v_i_2444_);
return v_target_2446_;
}
else
{
lean_object* v_es_2449_; lean_object* v___x_2450_; lean_object* v_source_2451_; lean_object* v_target_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_es_2449_ = lean_array_fget(v_source_2445_, v_i_2444_);
v___x_2450_ = lean_box(0);
v_source_2451_ = lean_array_fset(v_source_2445_, v_i_2444_, v___x_2450_);
v_target_2452_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2446_, v_es_2449_);
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_nat_add(v_i_2444_, v___x_2453_);
lean_dec(v_i_2444_);
v_i_2444_ = v___x_2454_;
v_source_2445_ = v_source_2451_;
v_target_2446_ = v_target_2452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_nbuckets_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2457_ = lean_array_get_size(v_data_2456_);
v___x_2458_ = lean_unsigned_to_nat(2u);
v_nbuckets_2459_ = lean_nat_mul(v___x_2457_, v___x_2458_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_mk_array(v_nbuckets_2459_, v___x_2461_);
v___x_2463_ = lean_array_propagate_mark(v_data_2456_, v___x_2462_);
v___x_2464_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2460_, v_data_2456_, v___x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2465_, lean_object* v_x_2466_){
_start:
{
if (lean_obj_tag(v_x_2466_) == 0)
{
uint8_t v___x_2467_; 
v___x_2467_ = 0;
return v___x_2467_;
}
else
{
lean_object* v_key_2468_; lean_object* v_tail_2469_; uint8_t v___x_2470_; 
v_key_2468_ = lean_ctor_get(v_x_2466_, 0);
v_tail_2469_ = lean_ctor_get(v_x_2466_, 2);
v___x_2470_ = l_Lean_ExprStructEq_beq(v_key_2468_, v_a_2465_);
if (v___x_2470_ == 0)
{
v_x_2466_ = v_tail_2469_;
goto _start;
}
else
{
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2472_, lean_object* v_x_2473_){
_start:
{
uint8_t v_res_2474_; lean_object* v_r_2475_; 
v_res_2474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2472_, v_x_2473_);
lean_dec(v_x_2473_);
lean_dec_ref(v_a_2472_);
v_r_2475_ = lean_box(v_res_2474_);
return v_r_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2476_, lean_object* v_a_2477_, lean_object* v_b_2478_){
_start:
{
lean_object* v_size_2479_; lean_object* v_buckets_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2523_; 
v_size_2479_ = lean_ctor_get(v_m_2476_, 0);
v_buckets_2480_ = lean_ctor_get(v_m_2476_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_m_2476_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2482_ = v_m_2476_;
v_isShared_2483_ = v_isSharedCheck_2523_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_buckets_2480_);
lean_inc(v_size_2479_);
lean_dec(v_m_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2523_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v_bkt_2497_; uint8_t v___x_2498_; 
v___x_2484_ = lean_array_get_size(v_buckets_2480_);
v___x_2485_ = l_Lean_ExprStructEq_hash(v_a_2477_);
v___x_2486_ = 32ULL;
v___x_2487_ = lean_uint64_shift_right(v___x_2485_, v___x_2486_);
v_fold_2488_ = lean_uint64_xor(v___x_2485_, v___x_2487_);
v___x_2489_ = 16ULL;
v___x_2490_ = lean_uint64_shift_right(v_fold_2488_, v___x_2489_);
v___x_2491_ = lean_uint64_xor(v_fold_2488_, v___x_2490_);
v___x_2492_ = lean_uint64_to_usize(v___x_2491_);
v___x_2493_ = lean_usize_of_nat(v___x_2484_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_sub(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_usize_land(v___x_2492_, v___x_2495_);
v_bkt_2497_ = lean_array_uget_borrowed(v_buckets_2480_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2477_, v_bkt_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v_size_x27_2500_; lean_object* v___x_2501_; lean_object* v_buckets_x27_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2499_ = lean_unsigned_to_nat(1u);
v_size_x27_2500_ = lean_nat_add(v_size_2479_, v___x_2499_);
lean_dec(v_size_2479_);
lean_inc(v_bkt_2497_);
v___x_2501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2477_);
lean_ctor_set(v___x_2501_, 1, v_b_2478_);
lean_ctor_set(v___x_2501_, 2, v_bkt_2497_);
v_buckets_x27_2502_ = lean_array_uset(v_buckets_2480_, v___x_2496_, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(4u);
v___x_2504_ = lean_nat_mul(v_size_x27_2500_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(3u);
v___x_2506_ = lean_nat_div(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_array_get_size(v_buckets_x27_2502_);
v___x_2508_ = lean_nat_dec_le(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
if (v___x_2508_ == 0)
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
v_val_2509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2502_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_val_2509_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2500_);
v___x_2511_ = v___x_2482_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2514_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_buckets_x27_2502_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2500_);
v___x_2514_ = v___x_2482_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_buckets_x27_2502_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v___x_2516_; lean_object* v_buckets_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v_bkt_2497_);
v___x_2516_ = lean_box(0);
v_buckets_x27_2517_ = lean_array_uset(v_buckets_2480_, v___x_2496_, v___x_2516_);
v___x_2518_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2477_, v_b_2478_, v_bkt_2497_);
v___x_2519_ = lean_array_uset(v_buckets_x27_2517_, v___x_2496_, v___x_2518_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2519_);
v___x_2521_ = v___x_2482_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_size_2479_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = lean_st_ref_take(v_a_2524_);
v___x_2529_ = lean_box(0);
v___x_2530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2528_, v_e_2525_, v_a_2526_);
v___x_2531_ = lean_st_ref_put(v_a_2524_, v___x_2530_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2532_, lean_object* v_e_2533_, lean_object* v_a_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2532_, v_e_2533_, v_a_2534_);
lean_dec(v_a_2532_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2537_, lean_object* v_x_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_apply_1(v_x_2538_, lean_box(0));
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2554_, lean_object* v_x_2555_){
_start:
{
if (lean_obj_tag(v_x_2555_) == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_box(0);
return v___x_2556_;
}
else
{
lean_object* v_key_2557_; lean_object* v_value_2558_; lean_object* v_tail_2559_; uint8_t v___x_2560_; 
v_key_2557_ = lean_ctor_get(v_x_2555_, 0);
v_value_2558_ = lean_ctor_get(v_x_2555_, 1);
v_tail_2559_ = lean_ctor_get(v_x_2555_, 2);
v___x_2560_ = l_Lean_ExprStructEq_beq(v_key_2557_, v_a_2554_);
if (v___x_2560_ == 0)
{
v_x_2555_ = v_tail_2559_;
goto _start;
}
else
{
lean_object* v___x_2562_; 
lean_inc(v_value_2558_);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_value_2558_);
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2563_, lean_object* v_x_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2563_, v_x_2564_);
lean_dec(v_x_2564_);
lean_dec_ref(v_a_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_buckets_2568_; lean_object* v___x_2569_; uint64_t v___x_2570_; uint64_t v___x_2571_; uint64_t v___x_2572_; uint64_t v_fold_2573_; uint64_t v___x_2574_; uint64_t v___x_2575_; uint64_t v___x_2576_; size_t v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_buckets_2568_ = lean_ctor_get(v_m_2566_, 1);
v___x_2569_ = lean_array_get_size(v_buckets_2568_);
v___x_2570_ = l_Lean_ExprStructEq_hash(v_a_2567_);
v___x_2571_ = 32ULL;
v___x_2572_ = lean_uint64_shift_right(v___x_2570_, v___x_2571_);
v_fold_2573_ = lean_uint64_xor(v___x_2570_, v___x_2572_);
v___x_2574_ = 16ULL;
v___x_2575_ = lean_uint64_shift_right(v_fold_2573_, v___x_2574_);
v___x_2576_ = lean_uint64_xor(v_fold_2573_, v___x_2575_);
v___x_2577_ = lean_uint64_to_usize(v___x_2576_);
v___x_2578_ = lean_usize_of_nat(v___x_2569_);
v___x_2579_ = ((size_t)1ULL);
v___x_2580_ = lean_usize_sub(v___x_2578_, v___x_2579_);
v___x_2581_ = lean_usize_land(v___x_2577_, v___x_2580_);
v___x_2582_ = lean_array_uget_borrowed(v_buckets_2568_, v___x_2581_);
v___x_2583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2567_, v___x_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2584_, v_a_2585_);
lean_dec_ref(v_a_2585_);
lean_dec_ref(v_m_2584_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2587_, lean_object* v___y_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2588_);
v___x_2595_ = lean_apply_7(v_k_2587_, v_b_2589_, v___y_2588_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, lean_box(0));
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2596_, lean_object* v___y_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2596_, v___y_2597_, v_b_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2605_, uint8_t v_bi_2606_, lean_object* v_type_2607_, lean_object* v_k_2608_, uint8_t v_kind_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___f_2616_; lean_object* v___x_2617_; 
lean_inc(v___y_2610_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2616_, 0, v_k_2608_);
lean_closure_set(v___f_2616_, 1, v___y_2610_);
v___x_2617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2605_, v_bi_2606_, v_type_2607_, v___f_2616_, v_kind_2609_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2617_) == 0)
{
return v___x_2617_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2626_, lean_object* v_bi_2627_, lean_object* v_type_2628_, lean_object* v_k_2629_, lean_object* v_kind_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v_bi_boxed_2637_; uint8_t v_kind_boxed_2638_; lean_object* v_res_2639_; 
v_bi_boxed_2637_ = lean_unbox(v_bi_2627_);
v_kind_boxed_2638_ = lean_unbox(v_kind_2630_);
v_res_2639_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2626_, v_bi_boxed_2637_, v_type_2628_, v_k_2629_, v_kind_boxed_2638_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2640_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2654_, lean_object* v_type_2655_, lean_object* v_val_2656_, lean_object* v_k_2657_, uint8_t v_nondep_2658_, uint8_t v_kind_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___f_2666_; lean_object* v___x_2667_; 
lean_inc(v___y_2660_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2666_, 0, v_k_2657_);
lean_closure_set(v___f_2666_, 1, v___y_2660_);
v___x_2667_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2654_, v_type_2655_, v_val_2656_, v___f_2666_, v_nondep_2658_, v_kind_2659_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2667_) == 0)
{
return v___x_2667_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2676_, lean_object* v_type_2677_, lean_object* v_val_2678_, lean_object* v_k_2679_, lean_object* v_nondep_2680_, lean_object* v_kind_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_nondep_boxed_2688_; uint8_t v_kind_boxed_2689_; lean_object* v_res_2690_; 
v_nondep_boxed_2688_ = lean_unbox(v_nondep_2680_);
v_kind_boxed_2689_ = lean_unbox(v_kind_2681_);
v_res_2690_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2676_, v_type_2677_, v_val_2678_, v_k_2679_, v_nondep_boxed_2688_, v_kind_boxed_2689_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = l_Lean_maxRecDepthErrorMessage;
v___x_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2699_ = l_Lean_MessageData_ofFormat(v___x_2698_);
return v___x_2699_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2701_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2702_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2703_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_ref_2703_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___y_2719_; lean_object* v_toCold_2728_; lean_object* v_currRecDepth_2729_; lean_object* v_ref_2730_; uint16_t v_optionFlags_2731_; uint8_t v_suppressElabErrors_2732_; uint8_t v_isRecordingDeps_2733_; lean_object* v_maxRecDepth_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v_toCold_2728_ = lean_ctor_get(v___y_2715_, 0);
v_currRecDepth_2729_ = lean_ctor_get(v___y_2715_, 1);
v_ref_2730_ = lean_ctor_get(v___y_2715_, 2);
v_optionFlags_2731_ = lean_ctor_get_uint16(v___y_2715_, sizeof(void*)*3);
v_suppressElabErrors_2732_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2733_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*3 + 3);
v_maxRecDepth_2739_ = lean_ctor_get(v_toCold_2728_, 3);
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_nat_dec_eq(v_maxRecDepth_2739_, v___x_2740_);
if (v___x_2741_ == 0)
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_nat_dec_eq(v_currRecDepth_2729_, v_maxRecDepth_2739_);
if (v___x_2742_ == 0)
{
goto v___jp_2734_;
}
else
{
lean_object* v___x_2743_; 
lean_dec_ref(v_x_2711_);
lean_inc(v_ref_2730_);
v___x_2743_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2730_);
v___y_2719_ = v___x_2743_;
goto v___jp_2718_;
}
}
else
{
goto v___jp_2734_;
}
v___jp_2718_:
{
if (lean_obj_tag(v___y_2719_) == 0)
{
return v___y_2719_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___y_2719_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___y_2719_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___y_2719_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___y_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
v___jp_2734_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_add(v_currRecDepth_2729_, v___x_2735_);
lean_inc(v_ref_2730_);
lean_inc_ref(v_toCold_2728_);
v___x_2737_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2737_, 0, v_toCold_2728_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
lean_ctor_set(v___x_2737_, 2, v_ref_2730_);
lean_ctor_set_uint16(v___x_2737_, sizeof(void*)*3, v_optionFlags_2731_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3 + 2, v_suppressElabErrors_2732_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3 + 3, v_isRecordingDeps_2733_);
lean_inc(v___y_2716_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2712_);
v___x_2738_ = lean_apply_6(v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___x_2737_, v___y_2716_, lean_box(0));
v___y_2719_ = v___x_2738_;
goto v___jp_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2752_, lean_object* v_pre_2753_, lean_object* v_post_2754_, lean_object* v_usedLetOnly_2755_, lean_object* v_skipConstInApp_2756_, lean_object* v_skipInstances_2757_, lean_object* v_body_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
uint8_t v_usedLetOnly_boxed_2766_; uint8_t v_skipConstInApp_boxed_2767_; uint8_t v_skipInstances_boxed_2768_; lean_object* v_res_2769_; 
v_usedLetOnly_boxed_2766_ = lean_unbox(v_usedLetOnly_2755_);
v_skipConstInApp_boxed_2767_ = lean_unbox(v_skipConstInApp_2756_);
v_skipInstances_boxed_2768_ = lean_unbox(v_skipInstances_2757_);
v_res_2769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2752_, v_pre_2753_, v_post_2754_, v_usedLetOnly_boxed_2766_, v_skipConstInApp_boxed_2767_, v_skipInstances_boxed_2768_, v_body_2758_, v_x_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2773_, lean_object* v_pre_2774_, lean_object* v_post_2775_, uint8_t v_usedLetOnly_2776_, uint8_t v_skipConstInApp_2777_, uint8_t v_skipInstances_2778_, lean_object* v_body_2779_, lean_object* v_x_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_array_push(v_fvars_2773_, v_x_2780_);
v___x_2788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2774_, v_post_2775_, v_usedLetOnly_2776_, v_skipConstInApp_2777_, v_skipInstances_2778_, v___x_2787_, v_body_2779_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2789_, lean_object* v_pre_2790_, lean_object* v_post_2791_, lean_object* v_usedLetOnly_2792_, lean_object* v_skipConstInApp_2793_, lean_object* v_skipInstances_2794_, lean_object* v_body_2795_, lean_object* v_x_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v_usedLetOnly_boxed_2803_; uint8_t v_skipConstInApp_boxed_2804_; uint8_t v_skipInstances_boxed_2805_; lean_object* v_res_2806_; 
v_usedLetOnly_boxed_2803_ = lean_unbox(v_usedLetOnly_2792_);
v_skipConstInApp_boxed_2804_ = lean_unbox(v_skipConstInApp_2793_);
v_skipInstances_boxed_2805_ = lean_unbox(v_skipInstances_2794_);
v_res_2806_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2789_, v_pre_2790_, v_post_2791_, v_usedLetOnly_boxed_2803_, v_skipConstInApp_boxed_2804_, v_skipInstances_boxed_2805_, v_body_2795_, v_x_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2807_, lean_object* v_post_2808_, uint8_t v_usedLetOnly_2809_, uint8_t v_skipConstInApp_2810_, uint8_t v_skipInstances_2811_, lean_object* v_e_2812_, lean_object* v_a_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
lean_inc_ref(v_post_2808_);
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc_ref(v_e_2812_);
v___x_2819_ = lean_apply_6(v_post_2808_, v_e_2812_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, lean_box(0));
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2838_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2838_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2838_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
switch(lean_obj_tag(v_a_2820_))
{
case 0:
{
lean_object* v_e_2824_; lean_object* v___x_2826_; 
lean_dec_ref(v_e_2812_);
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
v_e_2824_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_ref(v_e_2824_);
lean_dec_ref_known(v_a_2820_, 1);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_e_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_e_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
case 1:
{
lean_object* v_e_2828_; lean_object* v___x_2829_; 
lean_del_object(v___x_2822_);
lean_dec_ref(v_e_2812_);
v_e_2828_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_ref(v_e_2828_);
lean_dec_ref_known(v_a_2820_, 1);
v___x_2829_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2807_, v_post_2808_, v_usedLetOnly_2809_, v_skipConstInApp_2810_, v_skipInstances_2811_, v_e_2828_, v_a_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2829_;
}
default: 
{
lean_object* v_e_x3f_2830_; 
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
v_e_x3f_2830_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_e_x3f_2830_);
lean_dec_ref_known(v_a_2820_, 1);
if (lean_obj_tag(v_e_x3f_2830_) == 0)
{
lean_object* v___x_2832_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_e_2812_);
v___x_2832_ = v___x_2822_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_e_2812_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v_val_2834_; lean_object* v___x_2836_; 
lean_dec_ref(v_e_2812_);
v_val_2834_ = lean_ctor_get(v_e_x3f_2830_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v_e_x3f_2830_, 1);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_val_2834_);
v___x_2836_ = v___x_2822_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_val_2834_);
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
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_e_2812_);
lean_dec_ref(v_post_2808_);
lean_dec_ref(v_pre_2807_);
v_a_2839_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2819_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2819_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2847_, lean_object* v_post_2848_, uint8_t v_usedLetOnly_2849_, uint8_t v_skipConstInApp_2850_, uint8_t v_skipInstances_2851_, lean_object* v_fvars_2852_, lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
if (lean_obj_tag(v_e_2853_) == 6)
{
lean_object* v_binderName_2860_; lean_object* v_binderType_2861_; lean_object* v_body_2862_; uint8_t v_binderInfo_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_binderName_2860_ = lean_ctor_get(v_e_2853_, 0);
lean_inc(v_binderName_2860_);
v_binderType_2861_ = lean_ctor_get(v_e_2853_, 1);
lean_inc_ref(v_binderType_2861_);
v_body_2862_ = lean_ctor_get(v_e_2853_, 2);
lean_inc_ref(v_body_2862_);
v_binderInfo_2863_ = lean_ctor_get_uint8(v_e_2853_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2853_, 3);
v___x_2864_ = lean_box(v_usedLetOnly_2849_);
v___x_2865_ = lean_box(v_skipConstInApp_2850_);
v___x_2866_ = lean_box(v_skipInstances_2851_);
lean_inc_ref(v_post_2848_);
lean_inc_ref(v_pre_2847_);
lean_inc_ref(v_fvars_2852_);
v___f_2867_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2867_, 0, v_fvars_2852_);
lean_closure_set(v___f_2867_, 1, v_pre_2847_);
lean_closure_set(v___f_2867_, 2, v_post_2848_);
lean_closure_set(v___f_2867_, 3, v___x_2864_);
lean_closure_set(v___f_2867_, 4, v___x_2865_);
lean_closure_set(v___f_2867_, 5, v___x_2866_);
lean_closure_set(v___f_2867_, 6, v_body_2862_);
v___x_2868_ = lean_expr_instantiate_rev(v_binderType_2861_, v_fvars_2852_);
lean_dec_ref(v_fvars_2852_);
lean_dec_ref(v_binderType_2861_);
v___x_2869_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2847_, v_post_2848_, v_usedLetOnly_2849_, v_skipConstInApp_2850_, v_skipInstances_2851_, v___x_2868_, v_a_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = 0;
v___x_2872_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2860_, v_binderInfo_2863_, v_a_2870_, v___f_2867_, v___x_2871_, v_a_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2872_;
}
else
{
lean_dec_ref(v___f_2867_);
lean_dec(v_binderName_2860_);
return v___x_2869_;
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_expr_instantiate_rev(v_e_2853_, v_fvars_2852_);
lean_dec_ref(v_e_2853_);
lean_inc_ref(v_post_2848_);
lean_inc_ref(v_pre_2847_);
v___x_2874_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2847_, v_post_2848_, v_usedLetOnly_2849_, v_skipConstInApp_2850_, v_skipInstances_2851_, v___x_2873_, v_a_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; uint8_t v___x_2876_; uint8_t v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = 0;
v___x_2877_ = 1;
v___x_2878_ = 1;
v___x_2879_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2852_, v_a_2875_, v___x_2876_, v_usedLetOnly_2849_, v___x_2876_, v___x_2877_, v___x_2878_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec_ref(v_fvars_2852_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2847_, v_post_2848_, v_usedLetOnly_2849_, v_skipConstInApp_2850_, v_skipInstances_2851_, v_a_2880_, v_a_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2881_;
}
else
{
lean_dec_ref(v_post_2848_);
lean_dec_ref(v_pre_2847_);
return v___x_2879_;
}
}
else
{
lean_dec_ref(v_fvars_2852_);
lean_dec_ref(v_post_2848_);
lean_dec_ref(v_pre_2847_);
return v___x_2874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2882_, lean_object* v_pre_2883_, lean_object* v_post_2884_, uint8_t v_usedLetOnly_2885_, uint8_t v_skipConstInApp_2886_, uint8_t v_skipInstances_2887_, lean_object* v_body_2888_, lean_object* v_x_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_array_push(v_fvars_2882_, v_x_2889_);
v___x_2897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2883_, v_post_2884_, v_usedLetOnly_2885_, v_skipConstInApp_2886_, v_skipInstances_2887_, v___x_2896_, v_body_2888_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2898_, lean_object* v_pre_2899_, lean_object* v_post_2900_, lean_object* v_usedLetOnly_2901_, lean_object* v_skipConstInApp_2902_, lean_object* v_skipInstances_2903_, lean_object* v_body_2904_, lean_object* v_x_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_usedLetOnly_boxed_2912_; uint8_t v_skipConstInApp_boxed_2913_; uint8_t v_skipInstances_boxed_2914_; lean_object* v_res_2915_; 
v_usedLetOnly_boxed_2912_ = lean_unbox(v_usedLetOnly_2901_);
v_skipConstInApp_boxed_2913_ = lean_unbox(v_skipConstInApp_2902_);
v_skipInstances_boxed_2914_ = lean_unbox(v_skipInstances_2903_);
v_res_2915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2898_, v_pre_2899_, v_post_2900_, v_usedLetOnly_boxed_2912_, v_skipConstInApp_boxed_2913_, v_skipInstances_boxed_2914_, v_body_2904_, v_x_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2916_, lean_object* v_post_2917_, uint8_t v_usedLetOnly_2918_, uint8_t v_skipConstInApp_2919_, uint8_t v_skipInstances_2920_, lean_object* v_fvars_2921_, lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
if (lean_obj_tag(v_e_2922_) == 8)
{
lean_object* v_declName_2929_; lean_object* v_type_2930_; lean_object* v_value_2931_; lean_object* v_body_2932_; uint8_t v_nondep_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___f_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v_declName_2929_ = lean_ctor_get(v_e_2922_, 0);
lean_inc(v_declName_2929_);
v_type_2930_ = lean_ctor_get(v_e_2922_, 1);
lean_inc_ref(v_type_2930_);
v_value_2931_ = lean_ctor_get(v_e_2922_, 2);
lean_inc_ref(v_value_2931_);
v_body_2932_ = lean_ctor_get(v_e_2922_, 3);
lean_inc_ref(v_body_2932_);
v_nondep_2933_ = lean_ctor_get_uint8(v_e_2922_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2922_, 4);
v___x_2934_ = lean_box(v_usedLetOnly_2918_);
v___x_2935_ = lean_box(v_skipConstInApp_2919_);
v___x_2936_ = lean_box(v_skipInstances_2920_);
lean_inc_ref_n(v_post_2917_, 2);
lean_inc_ref_n(v_pre_2916_, 2);
lean_inc_ref(v_fvars_2921_);
v___f_2937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2937_, 0, v_fvars_2921_);
lean_closure_set(v___f_2937_, 1, v_pre_2916_);
lean_closure_set(v___f_2937_, 2, v_post_2917_);
lean_closure_set(v___f_2937_, 3, v___x_2934_);
lean_closure_set(v___f_2937_, 4, v___x_2935_);
lean_closure_set(v___f_2937_, 5, v___x_2936_);
lean_closure_set(v___f_2937_, 6, v_body_2932_);
v___x_2938_ = lean_expr_instantiate_rev(v_type_2930_, v_fvars_2921_);
lean_dec_ref(v_type_2930_);
v___x_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2916_, v_post_2917_, v_usedLetOnly_2918_, v_skipConstInApp_2919_, v_skipInstances_2920_, v___x_2938_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_expr_instantiate_rev(v_value_2931_, v_fvars_2921_);
lean_dec_ref(v_fvars_2921_);
lean_dec_ref(v_value_2931_);
v___x_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2916_, v_post_2917_, v_usedLetOnly_2918_, v_skipConstInApp_2919_, v_skipInstances_2920_, v___x_2941_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; uint8_t v___x_2944_; lean_object* v___x_2945_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = 0;
v___x_2945_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2929_, v_a_2940_, v_a_2943_, v___f_2937_, v_nondep_2933_, v___x_2944_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2945_;
}
else
{
lean_dec(v_a_2940_);
lean_dec_ref(v___f_2937_);
lean_dec(v_declName_2929_);
return v___x_2942_;
}
}
else
{
lean_dec_ref(v___f_2937_);
lean_dec_ref(v_value_2931_);
lean_dec(v_declName_2929_);
lean_dec_ref(v_fvars_2921_);
lean_dec_ref(v_post_2917_);
lean_dec_ref(v_pre_2916_);
return v___x_2939_;
}
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_expr_instantiate_rev(v_e_2922_, v_fvars_2921_);
lean_dec_ref(v_e_2922_);
lean_inc_ref(v_post_2917_);
lean_inc_ref(v_pre_2916_);
v___x_2947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2916_, v_post_2917_, v_usedLetOnly_2918_, v_skipConstInApp_2919_, v_skipInstances_2920_, v___x_2946_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; uint8_t v___x_2949_; uint8_t v___x_2950_; lean_object* v___x_2951_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = 0;
v___x_2950_ = 1;
v___x_2951_ = l_Lean_Meta_mkLetFVars(v_fvars_2921_, v_a_2948_, v_usedLetOnly_2918_, v___x_2949_, v___x_2950_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec_ref(v_fvars_2921_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2916_, v_post_2917_, v_usedLetOnly_2918_, v_skipConstInApp_2919_, v_skipInstances_2920_, v_a_2952_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2953_;
}
else
{
lean_dec_ref(v_post_2917_);
lean_dec_ref(v_pre_2916_);
return v___x_2951_;
}
}
else
{
lean_dec_ref(v_fvars_2921_);
lean_dec_ref(v_post_2917_);
lean_dec_ref(v_pre_2916_);
return v___x_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2954_, lean_object* v_post_2955_, uint8_t v_usedLetOnly_2956_, uint8_t v_skipConstInApp_2957_, uint8_t v_skipInstances_2958_, size_t v_sz_2959_, size_t v_i_2960_, lean_object* v_bs_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_usize_dec_lt(v_i_2960_, v_sz_2959_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
lean_dec_ref(v_post_2955_);
lean_dec_ref(v_pre_2954_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_bs_2961_);
return v___x_2969_;
}
else
{
lean_object* v_v_2970_; lean_object* v___x_2971_; lean_object* v_bs_x27_2972_; lean_object* v___x_2973_; 
v_v_2970_ = lean_array_uget(v_bs_2961_, v_i_2960_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v_bs_x27_2972_ = lean_array_uset(v_bs_2961_, v_i_2960_, v___x_2971_);
lean_inc_ref(v_post_2955_);
lean_inc_ref(v_pre_2954_);
v___x_2973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2954_, v_post_2955_, v_usedLetOnly_2956_, v_skipConstInApp_2957_, v_skipInstances_2958_, v_v_2970_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; size_t v___x_2975_; size_t v___x_2976_; lean_object* v___x_2977_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_i_2960_, v___x_2975_);
v___x_2977_ = lean_array_uset(v_bs_x27_2972_, v_i_2960_, v_a_2974_);
v_i_2960_ = v___x_2976_;
v_bs_2961_ = v___x_2977_;
goto _start;
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v_bs_x27_2972_);
lean_dec_ref(v_post_2955_);
lean_dec_ref(v_pre_2954_);
v_a_2979_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2973_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2973_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2987_, lean_object* v_post_2988_, uint8_t v_usedLetOnly_2989_, uint8_t v_skipConstInApp_2990_, uint8_t v_skipInstances_2991_, lean_object* v___x_2992_, lean_object* v___y_2993_, lean_object* v_b_2994_, lean_object* v_a_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2987_, v_post_2988_, v_usedLetOnly_2989_, v_skipConstInApp_2990_, v_skipInstances_2991_, v___x_2992_, v___y_2993_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3011_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3011_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3011_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3006_ = lean_array_fset(v_b_2994_, v_a_2995_, v_a_3002_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3007_);
v___x_3009_ = v___x_3004_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v_b_2994_);
v_a_3012_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3001_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3001_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3020_, lean_object* v_post_3021_, lean_object* v_usedLetOnly_3022_, lean_object* v_skipConstInApp_3023_, lean_object* v_skipInstances_3024_, lean_object* v___x_3025_, lean_object* v___y_3026_, lean_object* v_b_3027_, lean_object* v_a_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
uint8_t v_usedLetOnly_boxed_3034_; uint8_t v_skipConstInApp_boxed_3035_; uint8_t v_skipInstances_boxed_3036_; lean_object* v_res_3037_; 
v_usedLetOnly_boxed_3034_ = lean_unbox(v_usedLetOnly_3022_);
v_skipConstInApp_boxed_3035_ = lean_unbox(v_skipConstInApp_3023_);
v_skipInstances_boxed_3036_ = lean_unbox(v_skipInstances_3024_);
v_res_3037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3020_, v_post_3021_, v_usedLetOnly_boxed_3034_, v_skipConstInApp_boxed_3035_, v_skipInstances_boxed_3036_, v___x_3025_, v___y_3026_, v_b_3027_, v_a_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v_a_3028_);
lean_dec(v___y_3026_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3038_, lean_object* v___x_3039_, lean_object* v_pre_3040_, lean_object* v_post_3041_, uint8_t v_usedLetOnly_3042_, uint8_t v_skipConstInApp_3043_, uint8_t v_skipInstances_3044_, lean_object* v_a_3045_, lean_object* v_b_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___y_3054_; uint8_t v___x_3077_; 
v___x_3077_ = lean_nat_dec_lt(v_a_3045_, v_upperBound_3038_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
lean_dec(v_a_3045_);
lean_dec_ref(v_post_3041_);
lean_dec_ref(v_pre_3040_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_b_3046_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = lean_array_fget_borrowed(v_b_3046_, v_a_3045_);
v___x_3080_ = lean_array_get_size(v___x_3039_);
v___x_3081_ = lean_nat_dec_lt(v_a_3045_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___f_3085_; 
lean_inc(v___x_3079_);
v___x_3082_ = lean_box(v_usedLetOnly_3042_);
v___x_3083_ = lean_box(v_skipConstInApp_3043_);
v___x_3084_ = lean_box(v_skipInstances_3044_);
lean_inc(v_a_3045_);
lean_inc(v___y_3047_);
lean_inc_ref(v_post_3041_);
lean_inc_ref(v_pre_3040_);
v___f_3085_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3085_, 0, v_pre_3040_);
lean_closure_set(v___f_3085_, 1, v_post_3041_);
lean_closure_set(v___f_3085_, 2, v___x_3082_);
lean_closure_set(v___f_3085_, 3, v___x_3083_);
lean_closure_set(v___f_3085_, 4, v___x_3084_);
lean_closure_set(v___f_3085_, 5, v___x_3079_);
lean_closure_set(v___f_3085_, 6, v___y_3047_);
lean_closure_set(v___f_3085_, 7, v_b_3046_);
lean_closure_set(v___f_3085_, 8, v_a_3045_);
v___y_3054_ = v___f_3085_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3086_; uint8_t v_isInstance_3087_; 
v___x_3086_ = lean_array_fget_borrowed(v___x_3039_, v_a_3045_);
v_isInstance_3087_ = lean_ctor_get_uint8(v___x_3086_, sizeof(void*)*1 + 4);
if (v_isInstance_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___f_3091_; 
lean_inc(v___x_3079_);
v___x_3088_ = lean_box(v_usedLetOnly_3042_);
v___x_3089_ = lean_box(v_skipConstInApp_3043_);
v___x_3090_ = lean_box(v_skipInstances_3044_);
lean_inc(v_a_3045_);
lean_inc(v___y_3047_);
lean_inc_ref(v_post_3041_);
lean_inc_ref(v_pre_3040_);
v___f_3091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3091_, 0, v_pre_3040_);
lean_closure_set(v___f_3091_, 1, v_post_3041_);
lean_closure_set(v___f_3091_, 2, v___x_3088_);
lean_closure_set(v___f_3091_, 3, v___x_3089_);
lean_closure_set(v___f_3091_, 4, v___x_3090_);
lean_closure_set(v___f_3091_, 5, v___x_3079_);
lean_closure_set(v___f_3091_, 6, v___y_3047_);
lean_closure_set(v___f_3091_, 7, v_b_3046_);
lean_closure_set(v___f_3091_, 8, v_a_3045_);
v___y_3054_ = v___f_3091_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3092_; lean_object* v___f_3093_; 
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_b_3046_);
v___f_3093_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3093_, 0, v___x_3092_);
v___y_3054_ = v___f_3093_;
goto v___jp_3053_;
}
}
}
v___jp_3053_:
{
lean_object* v___x_3055_; 
lean_inc(v___y_3051_);
lean_inc_ref(v___y_3050_);
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
v___x_3055_ = lean_apply_5(v___y_3054_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, lean_box(0));
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3068_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3068_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3068_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
if (lean_obj_tag(v_a_3056_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; 
lean_dec(v_a_3045_);
lean_dec_ref(v_post_3041_);
lean_dec_ref(v_pre_3040_);
v_a_3060_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v_a_3056_, 1);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v_a_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_del_object(v___x_3058_);
v_a_3064_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v_a_3056_, 1);
v___x_3065_ = lean_unsigned_to_nat(1u);
v___x_3066_ = lean_nat_add(v_a_3045_, v___x_3065_);
lean_dec(v_a_3045_);
v_a_3045_ = v___x_3066_;
v_b_3046_ = v_a_3064_;
goto _start;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_3045_);
lean_dec_ref(v_post_3041_);
lean_dec_ref(v_pre_3040_);
v_a_3069_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3055_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3055_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3094_, lean_object* v_pre_3095_, lean_object* v_post_3096_, uint8_t v_usedLetOnly_3097_, uint8_t v_skipConstInApp_3098_, lean_object* v_x_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_f_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; 
if (lean_obj_tag(v_x_3099_) == 5)
{
lean_object* v_fn_3157_; lean_object* v_arg_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_fn_3157_ = lean_ctor_get(v_x_3099_, 0);
lean_inc_ref(v_fn_3157_);
v_arg_3158_ = lean_ctor_get(v_x_3099_, 1);
lean_inc_ref(v_arg_3158_);
lean_dec_ref_known(v_x_3099_, 2);
v___x_3159_ = lean_array_set(v_x_3100_, v_x_3101_, v_arg_3158_);
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_nat_sub(v_x_3101_, v___x_3160_);
lean_dec(v_x_3101_);
v_x_3099_ = v_fn_3157_;
v_x_3100_ = v___x_3159_;
v_x_3101_ = v___x_3161_;
goto _start;
}
else
{
lean_dec(v_x_3101_);
if (v_skipConstInApp_3098_ == 0)
{
goto v___jp_3154_;
}
else
{
uint8_t v___x_3163_; 
v___x_3163_ = l_Lean_Expr_isConst(v_x_3099_);
if (v___x_3163_ == 0)
{
goto v___jp_3154_;
}
else
{
v_f_3109_ = v_x_3099_;
v___y_3110_ = v___y_3102_;
v___y_3111_ = v___y_3103_;
v___y_3112_ = v___y_3104_;
v___y_3113_ = v___y_3105_;
v___y_3114_ = v___y_3106_;
goto v___jp_3108_;
}
}
}
v___jp_3108_:
{
if (v_skipInstances_3094_ == 0)
{
size_t v_sz_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v_sz_3115_ = lean_array_size(v_x_3100_);
v___x_3116_ = ((size_t)0ULL);
lean_inc_ref(v_post_3096_);
lean_inc_ref(v_pre_3095_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3094_, v_sz_3115_, v___x_3116_, v_x_3100_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l_Lean_mkAppN(v_f_3109_, v_a_3118_);
lean_dec(v_a_3118_);
v___x_3120_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3094_, v___x_3119_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
return v___x_3120_;
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v_f_3109_);
lean_dec_ref(v_post_3096_);
lean_dec_ref(v_pre_3095_);
v_a_3121_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3117_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_array_get_size(v_x_3100_);
lean_inc_ref(v_f_3109_);
v___x_3130_ = l_Lean_Meta_getFunInfoNArgs(v_f_3109_, v___x_3129_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v_paramInfo_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v_paramInfo_3132_ = lean_ctor_get(v_a_3131_, 0);
lean_inc_ref(v_paramInfo_3132_);
lean_dec(v_a_3131_);
v___x_3133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3096_);
lean_inc_ref(v_pre_3095_);
v___x_3134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3129_, v_paramInfo_3132_, v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3094_, v___x_3133_, v_x_3100_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec_ref(v_paramInfo_3132_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = l_Lean_mkAppN(v_f_3109_, v_a_3135_);
lean_dec(v_a_3135_);
v___x_3137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3094_, v___x_3136_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
return v___x_3137_;
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_f_3109_);
lean_dec_ref(v_post_3096_);
lean_dec_ref(v_pre_3095_);
v_a_3138_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3134_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3134_);
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
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_f_3109_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_post_3096_);
lean_dec_ref(v_pre_3095_);
v_a_3146_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3130_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3130_);
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
v___jp_3154_:
{
lean_object* v___x_3155_; 
lean_inc_ref(v_post_3096_);
lean_inc_ref(v_pre_3095_);
v___x_3155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3095_, v_post_3096_, v_usedLetOnly_3097_, v_skipConstInApp_3098_, v_skipInstances_3094_, v_x_3099_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v_f_3109_ = v_a_3156_;
v___y_3110_ = v___y_3102_;
v___y_3111_ = v___y_3103_;
v___y_3112_ = v___y_3104_;
v___y_3113_ = v___y_3105_;
v___y_3114_ = v___y_3106_;
goto v___jp_3108_;
}
else
{
lean_dec_ref(v_x_3100_);
lean_dec_ref(v_post_3096_);
lean_dec_ref(v_pre_3095_);
return v___x_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3164_, lean_object* v_pre_3165_, lean_object* v_e_3166_, lean_object* v_post_3167_, uint8_t v_usedLetOnly_3168_, uint8_t v_skipConstInApp_3169_, uint8_t v_skipInstances_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Core_checkSystem(v___x_3164_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v___x_3178_; 
lean_dec_ref_known(v___x_3177_, 1);
lean_inc_ref(v_pre_3165_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
lean_inc(v___y_3173_);
lean_inc_ref(v___y_3172_);
lean_inc_ref(v_e_3166_);
v___x_3178_ = lean_apply_6(v_pre_3165_, v_e_3166_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, lean_box(0));
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3227_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3227_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3227_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___y_3184_; 
switch(lean_obj_tag(v_a_3179_))
{
case 0:
{
lean_object* v_e_3219_; lean_object* v___x_3221_; 
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_e_3166_);
lean_dec_ref(v_pre_3165_);
v_e_3219_ = lean_ctor_get(v_a_3179_, 0);
lean_inc_ref(v_e_3219_);
lean_dec_ref_known(v_a_3179_, 1);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_e_3219_);
v___x_3221_ = v___x_3181_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_e_3219_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
case 1:
{
lean_object* v_e_3223_; lean_object* v___x_3224_; 
lean_del_object(v___x_3181_);
lean_dec_ref(v_e_3166_);
v_e_3223_ = lean_ctor_get(v_a_3179_, 0);
lean_inc_ref(v_e_3223_);
lean_dec_ref_known(v_a_3179_, 1);
v___x_3224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v_e_3223_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3224_;
}
default: 
{
lean_object* v_e_x3f_3225_; 
lean_del_object(v___x_3181_);
v_e_x3f_3225_ = lean_ctor_get(v_a_3179_, 0);
lean_inc(v_e_x3f_3225_);
lean_dec_ref_known(v_a_3179_, 1);
if (lean_obj_tag(v_e_x3f_3225_) == 0)
{
v___y_3184_ = v_e_3166_;
goto v___jp_3183_;
}
else
{
lean_object* v_val_3226_; 
lean_dec_ref(v_e_3166_);
v_val_3226_ = lean_ctor_get(v_e_x3f_3225_, 0);
lean_inc(v_val_3226_);
lean_dec_ref_known(v_e_x3f_3225_, 1);
v___y_3184_ = v_val_3226_;
goto v___jp_3183_;
}
}
}
v___jp_3183_:
{
switch(lean_obj_tag(v___y_3184_))
{
case 7:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___x_3185_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3186_;
}
case 6:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___x_3187_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3188_;
}
case 8:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___x_3189_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3190_;
}
case 5:
{
lean_object* v_dummy_3191_; lean_object* v_nargs_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_dummy_3191_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3192_ = l_Lean_Expr_getAppNumArgs(v___y_3184_);
lean_inc(v_nargs_3192_);
v___x_3193_ = lean_mk_array(v_nargs_3192_, v_dummy_3191_);
v___x_3194_ = lean_unsigned_to_nat(1u);
v___x_3195_ = lean_nat_sub(v_nargs_3192_, v___x_3194_);
lean_dec(v_nargs_3192_);
v___x_3196_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3170_, v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v___y_3184_, v___x_3193_, v___x_3195_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3196_;
}
case 10:
{
lean_object* v_data_3197_; lean_object* v_expr_3198_; lean_object* v___x_3199_; 
v_data_3197_ = lean_ctor_get(v___y_3184_, 0);
v_expr_3198_ = lean_ctor_get(v___y_3184_, 1);
lean_inc_ref(v_expr_3198_);
lean_inc_ref(v_post_3167_);
lean_inc_ref(v_pre_3165_);
v___x_3199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v_expr_3198_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; size_t v___x_3201_; size_t v___x_3202_; uint8_t v___x_3203_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = lean_ptr_addr(v_expr_3198_);
v___x_3202_ = lean_ptr_addr(v_a_3200_);
v___x_3203_ = lean_usize_dec_eq(v___x_3201_, v___x_3202_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_inc(v_data_3197_);
lean_dec_ref_known(v___y_3184_, 2);
v___x_3204_ = l_Lean_Expr_mdata___override(v_data_3197_, v_a_3200_);
v___x_3205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___x_3204_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; 
lean_dec(v_a_3200_);
v___x_3206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3206_;
}
}
else
{
lean_dec_ref_known(v___y_3184_, 2);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3165_);
return v___x_3199_;
}
}
case 11:
{
lean_object* v_typeName_3207_; lean_object* v_idx_3208_; lean_object* v_struct_3209_; lean_object* v___x_3210_; 
v_typeName_3207_ = lean_ctor_get(v___y_3184_, 0);
v_idx_3208_ = lean_ctor_get(v___y_3184_, 1);
v_struct_3209_ = lean_ctor_get(v___y_3184_, 2);
lean_inc_ref(v_struct_3209_);
lean_inc_ref(v_post_3167_);
lean_inc_ref(v_pre_3165_);
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v_struct_3209_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; size_t v___x_3212_; size_t v___x_3213_; uint8_t v___x_3214_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = lean_ptr_addr(v_struct_3209_);
v___x_3213_ = lean_ptr_addr(v_a_3211_);
v___x_3214_ = lean_usize_dec_eq(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc(v_idx_3208_);
lean_inc(v_typeName_3207_);
lean_dec_ref_known(v___y_3184_, 3);
v___x_3215_ = l_Lean_Expr_proj___override(v_typeName_3207_, v_idx_3208_, v_a_3211_);
v___x_3216_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___x_3215_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; 
lean_dec(v_a_3211_);
v___x_3217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3217_;
}
}
else
{
lean_dec_ref_known(v___y_3184_, 3);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3165_);
return v___x_3210_;
}
}
default: 
{
lean_object* v___x_3218_; 
v___x_3218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3165_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v___y_3184_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_e_3166_);
lean_dec_ref(v_pre_3165_);
v_a_3228_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3178_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3178_);
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
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_e_3166_);
lean_dec_ref(v_pre_3165_);
v_a_3236_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3177_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3177_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3244_, lean_object* v_pre_3245_, lean_object* v_e_3246_, lean_object* v_post_3247_, lean_object* v_usedLetOnly_3248_, lean_object* v_skipConstInApp_3249_, lean_object* v_skipInstances_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_usedLetOnly_boxed_3257_; uint8_t v_skipConstInApp_boxed_3258_; uint8_t v_skipInstances_boxed_3259_; lean_object* v_res_3260_; 
v_usedLetOnly_boxed_3257_ = lean_unbox(v_usedLetOnly_3248_);
v_skipConstInApp_boxed_3258_ = lean_unbox(v_skipConstInApp_3249_);
v_skipInstances_boxed_3259_ = lean_unbox(v_skipInstances_3250_);
v_res_3260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3244_, v_pre_3245_, v_e_3246_, v_post_3247_, v_usedLetOnly_boxed_3257_, v_skipConstInApp_boxed_3258_, v_skipInstances_boxed_3259_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3261_, lean_object* v_post_3262_, uint8_t v_usedLetOnly_3263_, uint8_t v_skipConstInApp_3264_, uint8_t v_skipInstances_3265_, lean_object* v_e_3266_, lean_object* v_a_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_inc(v_a_3267_);
v___x_3273_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3273_, 0, lean_box(0));
lean_closure_set(v___x_3273_, 1, lean_box(0));
lean_closure_set(v___x_3273_, 2, v_a_3267_);
v___x_3274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3273_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3309_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3309_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3309_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3275_, v_e_3266_);
lean_dec(v_a_3275_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; 
lean_del_object(v___x_3277_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3281_ = lean_box(v_usedLetOnly_3263_);
v___x_3282_ = lean_box(v_skipConstInApp_3264_);
v___x_3283_ = lean_box(v_skipInstances_3265_);
lean_inc_ref(v_e_3266_);
v___f_3284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3284_, 0, v___x_3280_);
lean_closure_set(v___f_3284_, 1, v_pre_3261_);
lean_closure_set(v___f_3284_, 2, v_e_3266_);
lean_closure_set(v___f_3284_, 3, v_post_3262_);
lean_closure_set(v___f_3284_, 4, v___x_3281_);
lean_closure_set(v___f_3284_, 5, v___x_3282_);
lean_closure_set(v___f_3284_, 6, v___x_3283_);
v___x_3285_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3284_, v_a_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc_n(v_a_3286_, 2);
lean_dec_ref_known(v___x_3285_, 1);
lean_inc(v_a_3267_);
v___f_3287_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3287_, 0, v_a_3267_);
lean_closure_set(v___f_3287_, 1, v_e_3266_);
lean_closure_set(v___f_3287_, 2, v_a_3286_);
v___x_3288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3287_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3295_ == 0)
{
lean_object* v_unused_3296_; 
v_unused_3296_ = lean_ctor_get(v___x_3288_, 0);
lean_dec(v_unused_3296_);
v___x_3290_ = v___x_3288_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_dec(v___x_3288_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v_a_3286_);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3286_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3286_);
v_a_3297_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3288_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3288_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_dec_ref(v_e_3266_);
return v___x_3285_;
}
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3307_; 
lean_dec_ref(v_e_3266_);
lean_dec_ref(v_post_3262_);
lean_dec_ref(v_pre_3261_);
v_val_3305_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___x_3279_, 1);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v_val_3305_);
v___x_3307_ = v___x_3277_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_val_3305_);
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
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v_e_3266_);
lean_dec_ref(v_post_3262_);
lean_dec_ref(v_pre_3261_);
v_a_3310_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3274_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3274_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3318_, lean_object* v_post_3319_, uint8_t v_usedLetOnly_3320_, uint8_t v_skipConstInApp_3321_, uint8_t v_skipInstances_3322_, lean_object* v_fvars_3323_, lean_object* v_e_3324_, lean_object* v_a_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
if (lean_obj_tag(v_e_3324_) == 7)
{
lean_object* v_binderName_3331_; lean_object* v_binderType_3332_; lean_object* v_body_3333_; uint8_t v_binderInfo_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_binderName_3331_ = lean_ctor_get(v_e_3324_, 0);
lean_inc(v_binderName_3331_);
v_binderType_3332_ = lean_ctor_get(v_e_3324_, 1);
lean_inc_ref(v_binderType_3332_);
v_body_3333_ = lean_ctor_get(v_e_3324_, 2);
lean_inc_ref(v_body_3333_);
v_binderInfo_3334_ = lean_ctor_get_uint8(v_e_3324_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3324_, 3);
v___x_3335_ = lean_box(v_usedLetOnly_3320_);
v___x_3336_ = lean_box(v_skipConstInApp_3321_);
v___x_3337_ = lean_box(v_skipInstances_3322_);
lean_inc_ref(v_post_3319_);
lean_inc_ref(v_pre_3318_);
lean_inc_ref(v_fvars_3323_);
v___f_3338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3338_, 0, v_fvars_3323_);
lean_closure_set(v___f_3338_, 1, v_pre_3318_);
lean_closure_set(v___f_3338_, 2, v_post_3319_);
lean_closure_set(v___f_3338_, 3, v___x_3335_);
lean_closure_set(v___f_3338_, 4, v___x_3336_);
lean_closure_set(v___f_3338_, 5, v___x_3337_);
lean_closure_set(v___f_3338_, 6, v_body_3333_);
v___x_3339_ = lean_expr_instantiate_rev(v_binderType_3332_, v_fvars_3323_);
lean_dec_ref(v_fvars_3323_);
lean_dec_ref(v_binderType_3332_);
v___x_3340_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3318_, v_post_3319_, v_usedLetOnly_3320_, v_skipConstInApp_3321_, v_skipInstances_3322_, v___x_3339_, v_a_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = 0;
v___x_3343_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3331_, v_binderInfo_3334_, v_a_3341_, v___f_3338_, v___x_3342_, v_a_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3343_;
}
else
{
lean_dec_ref(v___f_3338_);
lean_dec(v_binderName_3331_);
return v___x_3340_;
}
}
else
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_expr_instantiate_rev(v_e_3324_, v_fvars_3323_);
lean_dec_ref(v_e_3324_);
lean_inc_ref(v_post_3319_);
lean_inc_ref(v_pre_3318_);
v___x_3345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3318_, v_post_3319_, v_usedLetOnly_3320_, v_skipConstInApp_3321_, v_skipInstances_3322_, v___x_3344_, v_a_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = 0;
v___x_3348_ = 1;
v___x_3349_ = 1;
v___x_3350_ = l_Lean_Meta_mkForallFVars(v_fvars_3323_, v_a_3346_, v___x_3347_, v_usedLetOnly_3320_, v___x_3348_, v___x_3349_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec_ref(v_fvars_3323_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3318_, v_post_3319_, v_usedLetOnly_3320_, v_skipConstInApp_3321_, v_skipInstances_3322_, v_a_3351_, v_a_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3352_;
}
else
{
lean_dec_ref(v_post_3319_);
lean_dec_ref(v_pre_3318_);
return v___x_3350_;
}
}
else
{
lean_dec_ref(v_fvars_3323_);
lean_dec_ref(v_post_3319_);
lean_dec_ref(v_pre_3318_);
return v___x_3345_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3353_, lean_object* v_pre_3354_, lean_object* v_post_3355_, uint8_t v_usedLetOnly_3356_, uint8_t v_skipConstInApp_3357_, uint8_t v_skipInstances_3358_, lean_object* v_body_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_array_push(v_fvars_3353_, v_x_3360_);
v___x_3368_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3354_, v_post_3355_, v_usedLetOnly_3356_, v_skipConstInApp_3357_, v_skipInstances_3358_, v___x_3367_, v_body_3359_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3369_, lean_object* v_post_3370_, lean_object* v_usedLetOnly_3371_, lean_object* v_skipConstInApp_3372_, lean_object* v_skipInstances_3373_, lean_object* v_e_3374_, lean_object* v_a_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v_usedLetOnly_boxed_3381_; uint8_t v_skipConstInApp_boxed_3382_; uint8_t v_skipInstances_boxed_3383_; lean_object* v_res_3384_; 
v_usedLetOnly_boxed_3381_ = lean_unbox(v_usedLetOnly_3371_);
v_skipConstInApp_boxed_3382_ = lean_unbox(v_skipConstInApp_3372_);
v_skipInstances_boxed_3383_ = lean_unbox(v_skipInstances_3373_);
v_res_3384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3369_, v_post_3370_, v_usedLetOnly_boxed_3381_, v_skipConstInApp_boxed_3382_, v_skipInstances_boxed_3383_, v_e_3374_, v_a_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v_a_3375_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3385_, lean_object* v_post_3386_, lean_object* v_usedLetOnly_3387_, lean_object* v_skipConstInApp_3388_, lean_object* v_skipInstances_3389_, lean_object* v_sz_3390_, lean_object* v_i_3391_, lean_object* v_bs_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
uint8_t v_usedLetOnly_boxed_3399_; uint8_t v_skipConstInApp_boxed_3400_; uint8_t v_skipInstances_boxed_3401_; size_t v_sz_boxed_3402_; size_t v_i_boxed_3403_; lean_object* v_res_3404_; 
v_usedLetOnly_boxed_3399_ = lean_unbox(v_usedLetOnly_3387_);
v_skipConstInApp_boxed_3400_ = lean_unbox(v_skipConstInApp_3388_);
v_skipInstances_boxed_3401_ = lean_unbox(v_skipInstances_3389_);
v_sz_boxed_3402_ = lean_unbox_usize(v_sz_3390_);
lean_dec(v_sz_3390_);
v_i_boxed_3403_ = lean_unbox_usize(v_i_3391_);
lean_dec(v_i_3391_);
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3385_, v_post_3386_, v_usedLetOnly_boxed_3399_, v_skipConstInApp_boxed_3400_, v_skipInstances_boxed_3401_, v_sz_boxed_3402_, v_i_boxed_3403_, v_bs_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3405_, lean_object* v_post_3406_, lean_object* v_usedLetOnly_3407_, lean_object* v_skipConstInApp_3408_, lean_object* v_skipInstances_3409_, lean_object* v_e_3410_, lean_object* v_a_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
uint8_t v_usedLetOnly_boxed_3417_; uint8_t v_skipConstInApp_boxed_3418_; uint8_t v_skipInstances_boxed_3419_; lean_object* v_res_3420_; 
v_usedLetOnly_boxed_3417_ = lean_unbox(v_usedLetOnly_3407_);
v_skipConstInApp_boxed_3418_ = lean_unbox(v_skipConstInApp_3408_);
v_skipInstances_boxed_3419_ = lean_unbox(v_skipInstances_3409_);
v_res_3420_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3405_, v_post_3406_, v_usedLetOnly_boxed_3417_, v_skipConstInApp_boxed_3418_, v_skipInstances_boxed_3419_, v_e_3410_, v_a_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v_a_3411_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3421_, lean_object* v_post_3422_, lean_object* v_usedLetOnly_3423_, lean_object* v_skipConstInApp_3424_, lean_object* v_skipInstances_3425_, lean_object* v_fvars_3426_, lean_object* v_e_3427_, lean_object* v_a_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
uint8_t v_usedLetOnly_boxed_3434_; uint8_t v_skipConstInApp_boxed_3435_; uint8_t v_skipInstances_boxed_3436_; lean_object* v_res_3437_; 
v_usedLetOnly_boxed_3434_ = lean_unbox(v_usedLetOnly_3423_);
v_skipConstInApp_boxed_3435_ = lean_unbox(v_skipConstInApp_3424_);
v_skipInstances_boxed_3436_ = lean_unbox(v_skipInstances_3425_);
v_res_3437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3421_, v_post_3422_, v_usedLetOnly_boxed_3434_, v_skipConstInApp_boxed_3435_, v_skipInstances_boxed_3436_, v_fvars_3426_, v_e_3427_, v_a_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v_a_3428_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3438_, lean_object* v_post_3439_, lean_object* v_usedLetOnly_3440_, lean_object* v_skipConstInApp_3441_, lean_object* v_skipInstances_3442_, lean_object* v_fvars_3443_, lean_object* v_e_3444_, lean_object* v_a_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
uint8_t v_usedLetOnly_boxed_3451_; uint8_t v_skipConstInApp_boxed_3452_; uint8_t v_skipInstances_boxed_3453_; lean_object* v_res_3454_; 
v_usedLetOnly_boxed_3451_ = lean_unbox(v_usedLetOnly_3440_);
v_skipConstInApp_boxed_3452_ = lean_unbox(v_skipConstInApp_3441_);
v_skipInstances_boxed_3453_ = lean_unbox(v_skipInstances_3442_);
v_res_3454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3438_, v_post_3439_, v_usedLetOnly_boxed_3451_, v_skipConstInApp_boxed_3452_, v_skipInstances_boxed_3453_, v_fvars_3443_, v_e_3444_, v_a_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v_a_3445_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3455_, lean_object* v_post_3456_, lean_object* v_usedLetOnly_3457_, lean_object* v_skipConstInApp_3458_, lean_object* v_skipInstances_3459_, lean_object* v_fvars_3460_, lean_object* v_e_3461_, lean_object* v_a_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_usedLetOnly_boxed_3468_; uint8_t v_skipConstInApp_boxed_3469_; uint8_t v_skipInstances_boxed_3470_; lean_object* v_res_3471_; 
v_usedLetOnly_boxed_3468_ = lean_unbox(v_usedLetOnly_3457_);
v_skipConstInApp_boxed_3469_ = lean_unbox(v_skipConstInApp_3458_);
v_skipInstances_boxed_3470_ = lean_unbox(v_skipInstances_3459_);
v_res_3471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3455_, v_post_3456_, v_usedLetOnly_boxed_3468_, v_skipConstInApp_boxed_3469_, v_skipInstances_boxed_3470_, v_fvars_3460_, v_e_3461_, v_a_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v_a_3462_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3472_, lean_object* v___x_3473_, lean_object* v_pre_3474_, lean_object* v_post_3475_, lean_object* v_usedLetOnly_3476_, lean_object* v_skipConstInApp_3477_, lean_object* v_skipInstances_3478_, lean_object* v_a_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
uint8_t v_usedLetOnly_boxed_3487_; uint8_t v_skipConstInApp_boxed_3488_; uint8_t v_skipInstances_boxed_3489_; lean_object* v_res_3490_; 
v_usedLetOnly_boxed_3487_ = lean_unbox(v_usedLetOnly_3476_);
v_skipConstInApp_boxed_3488_ = lean_unbox(v_skipConstInApp_3477_);
v_skipInstances_boxed_3489_ = lean_unbox(v_skipInstances_3478_);
v_res_3490_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3472_, v___x_3473_, v_pre_3474_, v_post_3475_, v_usedLetOnly_boxed_3487_, v_skipConstInApp_boxed_3488_, v_skipInstances_boxed_3489_, v_a_3479_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___x_3473_);
lean_dec(v_upperBound_3472_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3491_, lean_object* v_pre_3492_, lean_object* v_post_3493_, lean_object* v_usedLetOnly_3494_, lean_object* v_skipConstInApp_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
uint8_t v_skipInstances_boxed_3505_; uint8_t v_usedLetOnly_boxed_3506_; uint8_t v_skipConstInApp_boxed_3507_; lean_object* v_res_3508_; 
v_skipInstances_boxed_3505_ = lean_unbox(v_skipInstances_3491_);
v_usedLetOnly_boxed_3506_ = lean_unbox(v_usedLetOnly_3494_);
v_skipConstInApp_boxed_3507_ = lean_unbox(v_skipConstInApp_3495_);
v_res_3508_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3505_, v_pre_3492_, v_post_3493_, v_usedLetOnly_boxed_3506_, v_skipConstInApp_boxed_3507_, v_x_3496_, v_x_3497_, v_x_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
return v_res_3508_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_box(0);
v___x_3510_ = lean_unsigned_to_nat(16u);
v___x_3511_ = lean_mk_array(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3516_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3516_, 0, lean_box(0));
lean_closure_set(v___x_3516_, 1, lean_box(0));
lean_closure_set(v___x_3516_, 2, v___x_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3517_, lean_object* v_pre_3518_, lean_object* v_post_3519_, uint8_t v_usedLetOnly_3520_, uint8_t v_skipConstInApp_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_a_3530_; lean_object* v___x_3531_; 
v___x_3527_ = 0;
v___x_3528_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3529_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3528_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3518_, v_post_3519_, v_usedLetOnly_3520_, v_skipConstInApp_3521_, v___x_3527_, v_input_3517_, v_a_3530_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3533_, 0, lean_box(0));
lean_closure_set(v___x_3533_, 1, lean_box(0));
lean_closure_set(v___x_3533_, 2, v_a_3530_);
v___x_3534_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3533_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; 
v_unused_3542_ = lean_ctor_get(v___x_3534_, 0);
lean_dec(v_unused_3542_);
v___x_3536_ = v___x_3534_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_dec(v___x_3534_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v_a_3532_);
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3532_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
else
{
lean_dec(v_a_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3543_, lean_object* v_pre_3544_, lean_object* v_post_3545_, lean_object* v_usedLetOnly_3546_, lean_object* v_skipConstInApp_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v_usedLetOnly_boxed_3553_; uint8_t v_skipConstInApp_boxed_3554_; lean_object* v_res_3555_; 
v_usedLetOnly_boxed_3553_ = lean_unbox(v_usedLetOnly_3546_);
v_skipConstInApp_boxed_3554_ = lean_unbox(v_skipConstInApp_3547_);
v_res_3555_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3543_, v_pre_3544_, v_post_3545_, v_usedLetOnly_boxed_3553_, v_skipConstInApp_boxed_3554_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3557_, lean_object* v_p_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; lean_object* v_a_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; 
v___f_3564_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3565_, 0, v_p_3558_);
v___x_3566_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3557_, v_a_3560_);
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = 0;
v___x_3569_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3567_, v___f_3564_, v___f_3565_, v___x_3568_, v___x_3568_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3570_, lean_object* v_p_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Meta_etaStructReduce(v_e_3570_, v_p_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3578_, lean_object* v___x_3579_, lean_object* v_pre_3580_, lean_object* v_post_3581_, uint8_t v_usedLetOnly_3582_, uint8_t v_skipConstInApp_3583_, uint8_t v_skipInstances_3584_, lean_object* v___x_3585_, lean_object* v_inst_3586_, lean_object* v_R_3587_, lean_object* v_a_3588_, lean_object* v_b_3589_, lean_object* v_c_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3578_, v___x_3579_, v_pre_3580_, v_post_3581_, v_usedLetOnly_3582_, v_skipConstInApp_3583_, v_skipInstances_3584_, v_a_3588_, v_b_3589_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3598_ = _args[0];
lean_object* v___x_3599_ = _args[1];
lean_object* v_pre_3600_ = _args[2];
lean_object* v_post_3601_ = _args[3];
lean_object* v_usedLetOnly_3602_ = _args[4];
lean_object* v_skipConstInApp_3603_ = _args[5];
lean_object* v_skipInstances_3604_ = _args[6];
lean_object* v___x_3605_ = _args[7];
lean_object* v_inst_3606_ = _args[8];
lean_object* v_R_3607_ = _args[9];
lean_object* v_a_3608_ = _args[10];
lean_object* v_b_3609_ = _args[11];
lean_object* v_c_3610_ = _args[12];
lean_object* v___y_3611_ = _args[13];
lean_object* v___y_3612_ = _args[14];
lean_object* v___y_3613_ = _args[15];
lean_object* v___y_3614_ = _args[16];
lean_object* v___y_3615_ = _args[17];
lean_object* v___y_3616_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3617_; uint8_t v_skipConstInApp_boxed_3618_; uint8_t v_skipInstances_boxed_3619_; lean_object* v_res_3620_; 
v_usedLetOnly_boxed_3617_ = lean_unbox(v_usedLetOnly_3602_);
v_skipConstInApp_boxed_3618_ = lean_unbox(v_skipConstInApp_3603_);
v_skipInstances_boxed_3619_ = lean_unbox(v_skipInstances_3604_);
v_res_3620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3598_, v___x_3599_, v_pre_3600_, v_post_3601_, v_usedLetOnly_boxed_3617_, v_skipConstInApp_boxed_3618_, v_skipInstances_boxed_3619_, v___x_3605_, v_inst_3606_, v_R_3607_, v_a_3608_, v_b_3609_, v_c_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec(v___x_3605_);
lean_dec_ref(v___x_3599_);
lean_dec(v_upperBound_3598_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3621_, lean_object* v_m_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3622_, v_a_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3625_, lean_object* v_m_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3625_, v_m_3626_, v_a_3627_);
lean_dec_ref(v_a_3627_);
lean_dec_ref(v_m_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3629_, lean_object* v_name_3630_, uint8_t v_bi_3631_, lean_object* v_type_3632_, lean_object* v_k_3633_, uint8_t v_kind_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3630_, v_bi_3631_, v_type_3632_, v_k_3633_, v_kind_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3642_, lean_object* v_name_3643_, lean_object* v_bi_3644_, lean_object* v_type_3645_, lean_object* v_k_3646_, lean_object* v_kind_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v_bi_boxed_3654_; uint8_t v_kind_boxed_3655_; lean_object* v_res_3656_; 
v_bi_boxed_3654_ = lean_unbox(v_bi_3644_);
v_kind_boxed_3655_ = lean_unbox(v_kind_3647_);
v_res_3656_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3642_, v_name_3643_, v_bi_boxed_3654_, v_type_3645_, v_k_3646_, v_kind_boxed_3655_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3657_, lean_object* v_name_3658_, lean_object* v_type_3659_, lean_object* v_val_3660_, lean_object* v_k_3661_, uint8_t v_nondep_3662_, uint8_t v_kind_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3658_, v_type_3659_, v_val_3660_, v_k_3661_, v_nondep_3662_, v_kind_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3671_, lean_object* v_name_3672_, lean_object* v_type_3673_, lean_object* v_val_3674_, lean_object* v_k_3675_, lean_object* v_nondep_3676_, lean_object* v_kind_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
uint8_t v_nondep_boxed_3684_; uint8_t v_kind_boxed_3685_; lean_object* v_res_3686_; 
v_nondep_boxed_3684_ = lean_unbox(v_nondep_3676_);
v_kind_boxed_3685_ = lean_unbox(v_kind_3677_);
v_res_3686_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3671_, v_name_3672_, v_type_3673_, v_val_3674_, v_k_3675_, v_nondep_boxed_3684_, v_kind_boxed_3685_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3687_, lean_object* v_ref_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3688_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3695_, lean_object* v_ref_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3695_, v_ref_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3712_, lean_object* v_x_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3712_, v_x_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3721_, lean_object* v_m_3722_, lean_object* v_a_3723_, lean_object* v_b_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3722_, v_a_3723_, v_b_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3726_, lean_object* v_a_3727_, lean_object* v_x_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3727_, v_x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3730_, lean_object* v_a_3731_, lean_object* v_x_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3730_, v_a_3731_, v_x_3732_);
lean_dec(v_x_3732_);
lean_dec_ref(v_a_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3734_, lean_object* v_a_3735_, lean_object* v_x_3736_){
_start:
{
uint8_t v___x_3737_; 
v___x_3737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3735_, v_x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3738_, lean_object* v_a_3739_, lean_object* v_x_3740_){
_start:
{
uint8_t v_res_3741_; lean_object* v_r_3742_; 
v_res_3741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3738_, v_a_3739_, v_x_3740_);
lean_dec(v_x_3740_);
lean_dec_ref(v_a_3739_);
v_r_3742_ = lean_box(v_res_3741_);
return v_r_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3743_, lean_object* v_data_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3746_, lean_object* v_a_3747_, lean_object* v_b_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3747_, v_b_3748_, v_x_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3751_, lean_object* v_i_3752_, lean_object* v_source_3753_, lean_object* v_target_3754_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3752_, v_source_3753_, v_target_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3756_, lean_object* v_x_3757_, lean_object* v_x_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3757_, v_x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3760_, lean_object* v_inst_3761_, lean_object* v_toBind_3762_, lean_object* v___f_3763_, lean_object* v_____do__lift_3764_){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3765_, 0, v_____do__lift_3764_);
lean_closure_set(v___x_3765_, 1, v_binderType_3760_);
v___x_3766_ = lean_apply_2(v_inst_3761_, lean_box(0), v___x_3765_);
v___x_3767_ = lean_apply_4(v_toBind_3762_, lean_box(0), lean_box(0), v___x_3766_, v___f_3763_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3768_, lean_object* v_usedFields_3769_, lean_object* v_binderName_3770_, lean_object* v_body_3771_, lean_object* v_val_3772_, lean_object* v_inst_3773_, lean_object* v_inst_3774_, lean_object* v_fieldVal_x3f_3775_, lean_object* v_____do__lift_3776_){
_start:
{
uint8_t v_____do__lift_291__boxed_3777_; lean_object* v_res_3778_; 
v_____do__lift_291__boxed_3777_ = lean_unbox(v_____do__lift_3776_);
v_res_3778_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3768_, v_usedFields_3769_, v_binderName_3770_, v_body_3771_, v_val_3772_, v_inst_3773_, v_inst_3774_, v_fieldVal_x3f_3775_, v_____do__lift_291__boxed_3777_);
lean_dec_ref(v_val_3772_);
lean_dec_ref(v_body_3771_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3779_, lean_object* v_usedFields_3780_, lean_object* v_binderName_3781_, lean_object* v_body_3782_, lean_object* v_inst_3783_, lean_object* v_inst_3784_, lean_object* v_fieldVal_x3f_3785_, lean_object* v_binderType_3786_, lean_object* v_toBind_3787_, lean_object* v_____x_3788_){
_start:
{
if (lean_obj_tag(v_____x_3788_) == 1)
{
lean_object* v_val_3789_; lean_object* v___f_3790_; lean_object* v___f_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_val_3789_ = lean_ctor_get(v_____x_3788_, 0);
lean_inc_n(v_val_3789_, 2);
lean_dec_ref_known(v_____x_3788_, 1);
lean_inc_n(v_inst_3784_, 2);
v___f_3790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3790_, 0, v_toPure_3779_);
lean_closure_set(v___f_3790_, 1, v_usedFields_3780_);
lean_closure_set(v___f_3790_, 2, v_binderName_3781_);
lean_closure_set(v___f_3790_, 3, v_body_3782_);
lean_closure_set(v___f_3790_, 4, v_val_3789_);
lean_closure_set(v___f_3790_, 5, v_inst_3783_);
lean_closure_set(v___f_3790_, 6, v_inst_3784_);
lean_closure_set(v___f_3790_, 7, v_fieldVal_x3f_3785_);
lean_inc(v_toBind_3787_);
v___f_3791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3791_, 0, v_binderType_3786_);
lean_closure_set(v___f_3791_, 1, v_inst_3784_);
lean_closure_set(v___f_3791_, 2, v_toBind_3787_);
lean_closure_set(v___f_3791_, 3, v___f_3790_);
v___x_3792_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3792_, 0, v_val_3789_);
v___x_3793_ = lean_apply_2(v_inst_3784_, lean_box(0), v___x_3792_);
v___x_3794_ = lean_apply_4(v_toBind_3787_, lean_box(0), lean_box(0), v___x_3793_, v___f_3791_);
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_dec(v_____x_3788_);
lean_dec(v_toBind_3787_);
lean_dec_ref(v_binderType_3786_);
lean_dec(v_fieldVal_x3f_3785_);
lean_dec(v_inst_3784_);
lean_dec_ref(v_inst_3783_);
lean_dec_ref(v_body_3782_);
lean_dec(v_binderName_3781_);
lean_dec(v_usedFields_3780_);
v___x_3795_ = lean_box(0);
v___x_3796_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3800_, lean_object* v_inst_3801_, lean_object* v_fieldVal_x3f_3802_, lean_object* v_usedFields_3803_, lean_object* v_e_3804_){
_start:
{
lean_object* v_toApplicative_3805_; lean_object* v_toBind_3806_; lean_object* v_toPure_3807_; 
v_toApplicative_3805_ = lean_ctor_get(v_inst_3800_, 0);
v_toBind_3806_ = lean_ctor_get(v_inst_3800_, 1);
v_toPure_3807_ = lean_ctor_get(v_toApplicative_3805_, 1);
lean_inc(v_toPure_3807_);
if (lean_obj_tag(v_e_3804_) == 6)
{
lean_object* v_binderName_3812_; lean_object* v_binderType_3813_; lean_object* v_body_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_inc_n(v_toBind_3806_, 2);
v_binderName_3812_ = lean_ctor_get(v_e_3804_, 0);
lean_inc_n(v_binderName_3812_, 2);
v_binderType_3813_ = lean_ctor_get(v_e_3804_, 1);
lean_inc_ref(v_binderType_3813_);
v_body_3814_ = lean_ctor_get(v_e_3804_, 2);
lean_inc_ref(v_body_3814_);
lean_dec_ref_known(v_e_3804_, 3);
lean_inc(v_fieldVal_x3f_3802_);
v___f_3815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3815_, 0, v_toPure_3807_);
lean_closure_set(v___f_3815_, 1, v_usedFields_3803_);
lean_closure_set(v___f_3815_, 2, v_binderName_3812_);
lean_closure_set(v___f_3815_, 3, v_body_3814_);
lean_closure_set(v___f_3815_, 4, v_inst_3800_);
lean_closure_set(v___f_3815_, 5, v_inst_3801_);
lean_closure_set(v___f_3815_, 6, v_fieldVal_x3f_3802_);
lean_closure_set(v___f_3815_, 7, v_binderType_3813_);
lean_closure_set(v___f_3815_, 8, v_toBind_3806_);
v___x_3816_ = lean_apply_1(v_fieldVal_x3f_3802_, v_binderName_3812_);
v___x_3817_ = lean_apply_4(v_toBind_3806_, lean_box(0), lean_box(0), v___x_3816_, v___f_3815_);
return v___x_3817_;
}
else
{
lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3834_; 
lean_dec(v_fieldVal_x3f_3802_);
lean_dec(v_inst_3801_);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_inst_3800_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; 
v_unused_3835_ = lean_ctor_get(v_inst_3800_, 1);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_inst_3800_, 0);
lean_dec(v_unused_3836_);
v___x_3819_ = v_inst_3800_;
v_isShared_3820_ = v_isSharedCheck_3834_;
goto v_resetjp_3818_;
}
else
{
lean_dec(v_inst_3800_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3834_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
lean_inc_ref(v_e_3804_);
v___x_3821_ = l_Lean_Expr_cleanupAnnotations(v_e_3804_);
v___x_3822_ = l_Lean_Expr_isApp(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_dec_ref(v___x_3821_);
lean_del_object(v___x_3819_);
goto v___jp_3808_;
}
else
{
lean_object* v_arg_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_arg_3823_ = lean_ctor_get(v___x_3821_, 1);
lean_inc_ref(v_arg_3823_);
v___x_3824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3821_);
v___x_3825_ = l_Lean_Expr_isApp(v___x_3824_);
if (v___x_3825_ == 0)
{
lean_dec_ref(v___x_3824_);
lean_dec_ref(v_arg_3823_);
lean_del_object(v___x_3819_);
goto v___jp_3808_;
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3824_);
v___x_3827_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3828_ = l_Lean_Expr_isConstOf(v___x_3826_, v___x_3827_);
lean_dec_ref(v___x_3826_);
if (v___x_3828_ == 0)
{
lean_dec_ref(v_arg_3823_);
lean_del_object(v___x_3819_);
goto v___jp_3808_;
}
else
{
lean_object* v___x_3830_; 
lean_dec_ref(v_e_3804_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 1, v_arg_3823_);
lean_ctor_set(v___x_3819_, 0, v_usedFields_3803_);
v___x_3830_ = v___x_3819_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_usedFields_3803_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_arg_3823_);
v___x_3830_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
v___x_3832_ = lean_apply_2(v_toPure_3807_, lean_box(0), v___x_3831_);
return v___x_3832_;
}
}
}
}
}
}
v___jp_3808_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_usedFields_3803_);
lean_ctor_set(v___x_3809_, 1, v_e_3804_);
v___x_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
v___x_3811_ = lean_apply_2(v_toPure_3807_, lean_box(0), v___x_3810_);
return v___x_3811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3837_, lean_object* v_usedFields_3838_, lean_object* v_binderName_3839_, lean_object* v_body_3840_, lean_object* v_val_3841_, lean_object* v_inst_3842_, lean_object* v_inst_3843_, lean_object* v_fieldVal_x3f_3844_, uint8_t v_____do__lift_3845_){
_start:
{
if (v_____do__lift_3845_ == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_dec(v_fieldVal_x3f_3844_);
lean_dec(v_inst_3843_);
lean_dec_ref(v_inst_3842_);
lean_dec(v_binderName_3839_);
lean_dec(v_usedFields_3838_);
v___x_3846_ = lean_box(0);
v___x_3847_ = lean_apply_2(v_toPure_3837_, lean_box(0), v___x_3846_);
return v___x_3847_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec(v_toPure_3837_);
v___x_3848_ = l_Lean_NameSet_insert(v_usedFields_3838_, v_binderName_3839_);
v___x_3849_ = lean_expr_instantiate1(v_body_3840_, v_val_3841_);
v___x_3850_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3842_, v_inst_3843_, v_fieldVal_x3f_3844_, v___x_3848_, v___x_3849_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3851_, lean_object* v_inst_3852_, lean_object* v_inst_3853_, lean_object* v_fieldVal_x3f_3854_, lean_object* v_usedFields_3855_, lean_object* v_e_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3852_, v_inst_3853_, v_fieldVal_x3f_3854_, v_usedFields_3855_, v_e_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3858_, lean_object* v_inst_3859_, lean_object* v_fieldVal_x3f_3860_, lean_object* v_toPure_3861_, lean_object* v_____s_3862_){
_start:
{
lean_object* v_fst_3863_; 
v_fst_3863_ = lean_ctor_get(v_____s_3862_, 0);
if (lean_obj_tag(v_fst_3863_) == 0)
{
lean_object* v_snd_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec(v_toPure_3861_);
v_snd_3864_ = lean_ctor_get(v_____s_3862_, 1);
lean_inc(v_snd_3864_);
lean_dec_ref(v_____s_3862_);
v___x_3865_ = l_Lean_NameSet_empty;
v___x_3866_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3858_, v_inst_3859_, v_fieldVal_x3f_3860_, v___x_3865_, v_snd_3864_);
return v___x_3866_;
}
else
{
lean_object* v_val_3867_; lean_object* v___x_3868_; 
lean_inc_ref(v_fst_3863_);
lean_dec_ref(v_____s_3862_);
lean_dec(v_fieldVal_x3f_3860_);
lean_dec(v_inst_3859_);
lean_dec_ref(v_inst_3858_);
v_val_3867_ = lean_ctor_get(v_fst_3863_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v_fst_3863_, 1);
v___x_3868_ = lean_apply_2(v_toPure_3861_, lean_box(0), v_val_3867_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3869_, lean_object* v_a_3870_, lean_object* v___x_3871_, lean_object* v_toPure_3872_, lean_object* v_____r_3873_){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_expr_instantiate1(v_body_3869_, v_a_3870_);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3871_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
v___x_3877_ = lean_apply_2(v_toPure_3872_, lean_box(0), v___x_3876_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3878_, lean_object* v_a_3879_, lean_object* v___x_3880_, lean_object* v_toPure_3881_, lean_object* v_____r_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3878_, v_a_3879_, v___x_3880_, v_toPure_3881_, v_____r_3882_);
lean_dec_ref(v_a_3879_);
lean_dec_ref(v_body_3878_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3886_, lean_object* v_toPure_3887_, lean_object* v___f_3888_, uint8_t v_____do__lift_3889_){
_start:
{
if (v_____do__lift_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec(v___f_3888_);
v___x_3890_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v_snd_3886_);
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
v___x_3893_ = lean_apply_2(v_toPure_3887_, lean_box(0), v___x_3892_);
return v___x_3893_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_toPure_3887_);
lean_dec(v_snd_3886_);
v___x_3894_ = lean_box(0);
v___x_3895_ = lean_apply_1(v___f_3888_, v___x_3894_);
return v___x_3895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3896_, lean_object* v_toPure_3897_, lean_object* v___f_3898_, lean_object* v_____do__lift_3899_){
_start:
{
uint8_t v_____do__lift_566__boxed_3900_; lean_object* v_res_3901_; 
v_____do__lift_566__boxed_3900_ = lean_unbox(v_____do__lift_3899_);
v_res_3901_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3896_, v_toPure_3897_, v___f_3898_, v_____do__lift_566__boxed_3900_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3902_, lean_object* v_inst_3903_, lean_object* v_toBind_3904_, lean_object* v___f_3905_, lean_object* v_____do__lift_3906_){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3907_, 0, v_____do__lift_3906_);
lean_closure_set(v___x_3907_, 1, v_binderType_3902_);
v___x_3908_ = lean_apply_2(v_inst_3903_, lean_box(0), v___x_3907_);
v___x_3909_ = lean_apply_4(v_toBind_3904_, lean_box(0), lean_box(0), v___x_3908_, v___f_3905_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3910_, lean_object* v_toPure_3911_, lean_object* v_levels_x3f_3912_, lean_object* v_inst_3913_, lean_object* v_toBind_3914_, lean_object* v_a_3915_, lean_object* v_x_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v_snd_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3938_; 
v_snd_3918_ = lean_ctor_get(v___y_3917_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___y_3917_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v___y_3917_, 0);
lean_dec(v_unused_3939_);
v___x_3920_ = v___y_3917_;
v_isShared_3921_ = v_isSharedCheck_3938_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_snd_3918_);
lean_dec(v___y_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3938_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_snd_3918_) == 6)
{
lean_object* v_binderType_3922_; lean_object* v_body_3923_; lean_object* v___f_3924_; 
lean_del_object(v___x_3920_);
v_binderType_3922_ = lean_ctor_get(v_snd_3918_, 1);
lean_inc_ref(v_binderType_3922_);
v_body_3923_ = lean_ctor_get(v_snd_3918_, 2);
lean_inc(v_toPure_3911_);
lean_inc(v___x_3910_);
lean_inc_ref(v_a_3915_);
lean_inc_ref(v_body_3923_);
v___f_3924_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3924_, 0, v_body_3923_);
lean_closure_set(v___f_3924_, 1, v_a_3915_);
lean_closure_set(v___f_3924_, 2, v___x_3910_);
lean_closure_set(v___f_3924_, 3, v_toPure_3911_);
if (lean_obj_tag(v_levels_x3f_3912_) == 0)
{
lean_object* v___f_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec(v___x_3910_);
v___f_3925_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3925_, 0, v_snd_3918_);
lean_closure_set(v___f_3925_, 1, v_toPure_3911_);
lean_closure_set(v___f_3925_, 2, v___f_3924_);
lean_inc(v_toBind_3914_);
lean_inc(v_inst_3913_);
v___f_3926_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3926_, 0, v_binderType_3922_);
lean_closure_set(v___f_3926_, 1, v_inst_3913_);
lean_closure_set(v___f_3926_, 2, v_toBind_3914_);
lean_closure_set(v___f_3926_, 3, v___f_3925_);
v___x_3927_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3927_, 0, v_a_3915_);
v___x_3928_ = lean_apply_2(v_inst_3913_, lean_box(0), v___x_3927_);
v___x_3929_ = lean_apply_4(v_toBind_3914_, lean_box(0), lean_box(0), v___x_3928_, v___f_3926_);
return v___x_3929_;
}
else
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_inc_ref(v_body_3923_);
lean_dec_ref(v___f_3924_);
lean_dec_ref_known(v_snd_3918_, 3);
lean_dec_ref(v_binderType_3922_);
lean_dec(v_toBind_3914_);
lean_dec(v_inst_3913_);
v___x_3930_ = lean_box(0);
v___x_3931_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3923_, v_a_3915_, v___x_3910_, v_toPure_3911_, v___x_3930_);
lean_dec_ref(v_a_3915_);
lean_dec_ref(v_body_3923_);
return v___x_3931_;
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec_ref(v_a_3915_);
lean_dec(v_toBind_3914_);
lean_dec(v_inst_3913_);
lean_dec(v___x_3910_);
v___x_3932_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3932_);
v___x_3934_ = v___x_3920_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_snd_3918_);
v___x_3934_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
v___x_3936_ = lean_apply_2(v_toPure_3911_, lean_box(0), v___x_3935_);
return v___x_3936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3940_, lean_object* v_toPure_3941_, lean_object* v_levels_x3f_3942_, lean_object* v_inst_3943_, lean_object* v_toBind_3944_, lean_object* v_a_3945_, lean_object* v_x_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3940_, v_toPure_3941_, v_levels_x3f_3942_, v_inst_3943_, v_toBind_3944_, v_a_3945_, v_x_3946_, v___y_3947_);
lean_dec(v_levels_x3f_3942_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3949_, lean_object* v_levels_x3f_3950_, lean_object* v_inst_3951_, lean_object* v_toBind_3952_, lean_object* v_params_3953_, lean_object* v_inst_3954_, lean_object* v___f_3955_, lean_object* v_val_3956_){
_start:
{
lean_object* v___x_3957_; lean_object* v___f_3958_; lean_object* v___x_3959_; size_t v_sz_3960_; size_t v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3957_ = lean_box(0);
lean_inc(v_toBind_3952_);
v___f_3958_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3958_, 0, v___x_3957_);
lean_closure_set(v___f_3958_, 1, v_toPure_3949_);
lean_closure_set(v___f_3958_, 2, v_levels_x3f_3950_);
lean_closure_set(v___f_3958_, 3, v_inst_3951_);
lean_closure_set(v___f_3958_, 4, v_toBind_3952_);
v___x_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v_val_3956_);
v_sz_3960_ = lean_array_size(v_params_3953_);
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3954_, v_params_3953_, v___f_3958_, v_sz_3960_, v___x_3961_, v___x_3959_);
v___x_3963_ = lean_apply_4(v_toBind_3952_, lean_box(0), lean_box(0), v___x_3962_, v___f_3955_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3964_, lean_object* v_us_3965_, uint8_t v___x_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3964_, v_us_3965_, v___x_3966_, v___y_3969_, v___y_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3973_, lean_object* v_us_3974_, lean_object* v___x_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v___x_677__boxed_3981_; lean_object* v_res_3982_; 
v___x_677__boxed_3981_ = lean_unbox(v___x_3975_);
v_res_3982_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3973_, v_us_3974_, v___x_677__boxed_3981_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec_ref(v_cinfo_3973_);
return v_res_3982_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3986_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_3987_ = lean_unsigned_to_nat(2u);
v___x_3988_ = lean_unsigned_to_nat(202u);
v___x_3989_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_3990_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_3991_ = l_mkPanicMessageWithDecl(v___x_3990_, v___x_3989_, v___x_3988_, v___x_3987_, v___x_3986_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_3992_, lean_object* v___x_3993_, lean_object* v_inst_3994_, lean_object* v_toBind_3995_, lean_object* v___f_3996_, lean_object* v_us_3997_){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3998_ = l_List_lengthTR___redArg(v_us_3997_);
v___x_3999_ = l_Lean_ConstantInfo_levelParams(v_cinfo_3992_);
v___x_4000_ = l_List_lengthTR___redArg(v___x_3999_);
lean_dec(v___x_3999_);
v___x_4001_ = lean_nat_dec_eq(v___x_3998_, v___x_4000_);
lean_dec(v___x_4000_);
lean_dec(v___x_3998_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec(v_us_3997_);
lean_dec(v___f_3996_);
lean_dec(v_toBind_3995_);
lean_dec(v_inst_3994_);
lean_dec_ref(v_cinfo_3992_);
v___x_4002_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4003_ = l_panic___redArg(v___x_3993_, v___x_4002_);
return v___x_4003_;
}
else
{
uint8_t v___x_4004_; lean_object* v___x_4005_; lean_object* v___f_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4004_ = 0;
v___x_4005_ = lean_box(v___x_4004_);
v___f_4006_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4006_, 0, v_cinfo_3992_);
lean_closure_set(v___f_4006_, 1, v_us_3997_);
lean_closure_set(v___f_4006_, 2, v___x_4005_);
v___x_4007_ = lean_apply_2(v_inst_3994_, lean_box(0), v___f_4006_);
v___x_4008_ = lean_apply_4(v_toBind_3995_, lean_box(0), lean_box(0), v___x_4007_, v___f_3996_);
return v___x_4008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4009_, lean_object* v___x_4010_, lean_object* v_inst_4011_, lean_object* v_toBind_4012_, lean_object* v___f_4013_, lean_object* v_us_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4009_, v___x_4010_, v_inst_4011_, v_toBind_4012_, v___f_4013_, v_us_4014_);
lean_dec(v___x_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4016_, lean_object* v_inst_4017_, lean_object* v_toBind_4018_, lean_object* v___f_4019_, lean_object* v_levels_x3f_4020_, lean_object* v_toPure_4021_, lean_object* v_cinfo_4022_){
_start:
{
lean_object* v___f_4023_; 
lean_inc(v_toBind_4018_);
lean_inc(v_inst_4017_);
lean_inc_ref(v_cinfo_4022_);
v___f_4023_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4023_, 0, v_cinfo_4022_);
lean_closure_set(v___f_4023_, 1, v___x_4016_);
lean_closure_set(v___f_4023_, 2, v_inst_4017_);
lean_closure_set(v___f_4023_, 3, v_toBind_4018_);
lean_closure_set(v___f_4023_, 4, v___f_4019_);
if (lean_obj_tag(v_levels_x3f_4020_) == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v_toPure_4021_);
v___x_4024_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4024_, 0, v_cinfo_4022_);
v___x_4025_ = lean_apply_2(v_inst_4017_, lean_box(0), v___x_4024_);
v___x_4026_ = lean_apply_4(v_toBind_4018_, lean_box(0), lean_box(0), v___x_4025_, v___f_4023_);
return v___x_4026_;
}
else
{
lean_object* v_val_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
lean_dec_ref(v_cinfo_4022_);
lean_dec(v_inst_4017_);
v_val_4027_ = lean_ctor_get(v_levels_x3f_4020_, 0);
lean_inc(v_val_4027_);
lean_dec_ref_known(v_levels_x3f_4020_, 1);
v___x_4028_ = lean_apply_2(v_toPure_4021_, lean_box(0), v_val_4027_);
v___x_4029_ = lean_apply_4(v_toBind_4018_, lean_box(0), lean_box(0), v___x_4028_, v___f_4023_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4030_, lean_object* v_inst_4031_, lean_object* v_inst_4032_, lean_object* v_inst_4033_, lean_object* v_defaultFn_4034_, lean_object* v_levels_x3f_4035_, lean_object* v_params_4036_, lean_object* v_fieldVal_x3f_4037_){
_start:
{
lean_object* v_toApplicative_4038_; lean_object* v_toBind_4039_; lean_object* v_toPure_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___f_4043_; lean_object* v___f_4044_; lean_object* v___x_4045_; lean_object* v___f_4046_; lean_object* v___x_4047_; 
v_toApplicative_4038_ = lean_ctor_get(v_inst_4030_, 0);
v_toBind_4039_ = lean_ctor_get(v_inst_4030_, 1);
lean_inc_n(v_toBind_4039_, 3);
v_toPure_4040_ = lean_ctor_get(v_toApplicative_4038_, 1);
lean_inc_n(v_toPure_4040_, 3);
v___x_4041_ = lean_box(0);
lean_inc_ref_n(v_inst_4030_, 3);
v___x_4042_ = l_Lean_getConstInfo___redArg(v_inst_4030_, v_inst_4031_, v_inst_4032_, v_defaultFn_4034_);
lean_inc_n(v_inst_4033_, 2);
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4043_, 0, v_inst_4030_);
lean_closure_set(v___f_4043_, 1, v_inst_4033_);
lean_closure_set(v___f_4043_, 2, v_fieldVal_x3f_4037_);
lean_closure_set(v___f_4043_, 3, v_toPure_4040_);
lean_inc(v_levels_x3f_4035_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4044_, 0, v_toPure_4040_);
lean_closure_set(v___f_4044_, 1, v_levels_x3f_4035_);
lean_closure_set(v___f_4044_, 2, v_inst_4033_);
lean_closure_set(v___f_4044_, 3, v_toBind_4039_);
lean_closure_set(v___f_4044_, 4, v_params_4036_);
lean_closure_set(v___f_4044_, 5, v_inst_4030_);
lean_closure_set(v___f_4044_, 6, v___f_4043_);
v___x_4045_ = l_instInhabitedOfMonad___redArg(v_inst_4030_, v___x_4041_);
v___f_4046_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4046_, 0, v___x_4045_);
lean_closure_set(v___f_4046_, 1, v_inst_4033_);
lean_closure_set(v___f_4046_, 2, v_toBind_4039_);
lean_closure_set(v___f_4046_, 3, v___f_4044_);
lean_closure_set(v___f_4046_, 4, v_levels_x3f_4035_);
lean_closure_set(v___f_4046_, 5, v_toPure_4040_);
v___x_4047_ = lean_apply_4(v_toBind_4039_, lean_box(0), lean_box(0), v___x_4042_, v___f_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4048_, lean_object* v_inst_4049_, lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_defaultFn_4054_, lean_object* v_levels_x3f_4055_, lean_object* v_params_4056_, lean_object* v_fieldVal_x3f_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4049_, v_inst_4050_, v_inst_4051_, v_inst_4052_, v_defaultFn_4054_, v_levels_x3f_4055_, v_params_4056_, v_fieldVal_x3f_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4059_, lean_object* v_inst_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_, lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v_defaultFn_4065_, lean_object* v_levels_x3f_4066_, lean_object* v_params_4067_, lean_object* v_fieldVal_x3f_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4059_, v_inst_4060_, v_inst_4061_, v_inst_4062_, v_inst_4063_, v_inst_4064_, v_defaultFn_4065_, v_levels_x3f_4066_, v_params_4067_, v_fieldVal_x3f_4068_);
lean_dec_ref(v_inst_4064_);
return v_res_4069_;
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
