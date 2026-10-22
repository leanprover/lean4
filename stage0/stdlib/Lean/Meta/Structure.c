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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_etaStructReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaStructReduce___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_etaStructReduce___closed__0 = (const lean_object*)&l_Lean_Meta_etaStructReduce___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_390_; lean_object* v_currRecDepth_391_; lean_object* v_ref_392_; uint16_t v_optionFlags_393_; uint8_t v_suppressElabErrors_394_; uint8_t v_isRecordingDeps_395_; lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_toCold_390_ = lean_ctor_get(v___y_387_, 0);
v_currRecDepth_391_ = lean_ctor_get(v___y_387_, 1);
v_ref_392_ = lean_ctor_get(v___y_387_, 2);
v_optionFlags_393_ = lean_ctor_get_uint16(v___y_387_, sizeof(void*)*3);
v_suppressElabErrors_394_ = lean_ctor_get_uint8(v___y_387_, sizeof(void*)*3 + 2);
v_isRecordingDeps_395_ = lean_ctor_get_uint8(v___y_387_, sizeof(void*)*3 + 3);
v_ref_396_ = l_Lean_replaceRef(v_ref_383_, v_ref_392_);
lean_inc(v_currRecDepth_391_);
lean_inc_ref(v_toCold_390_);
v___x_397_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_397_, 0, v_toCold_390_);
lean_ctor_set(v___x_397_, 1, v_currRecDepth_391_);
lean_ctor_set(v___x_397_, 2, v_ref_396_);
lean_ctor_set_uint16(v___x_397_, sizeof(void*)*3, v_optionFlags_393_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 2, v_suppressElabErrors_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 3, v_isRecordingDeps_395_);
v___x_398_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_384_, v___y_385_, v___y_386_, v___x_397_, v___y_388_);
lean_dec_ref_known(v___x_397_, 3);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(lean_object* v_ref_399_, lean_object* v_msg_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_399_, v_msg_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v_ref_399_);
return v_res_406_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2));
v___x_412_ = l_Lean_stringToMessageData(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(uint8_t v___x_416_, lean_object* v_projName_417_, lean_object* v_n_418_, lean_object* v_ref_419_, lean_object* v___f_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
if (v___x_416_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_426_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
v___x_427_ = l_Lean_MessageData_ofName(v_projName_417_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_MessageData_ofConstName(v_n_418_, v___x_416_);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_432_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_419_, v___x_434_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
v___x_437_ = lean_apply_6(v___f_420_, v_a_436_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, lean_box(0));
return v___x_437_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v___f_420_);
v_a_438_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_435_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_435_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_n_418_);
lean_dec(v_projName_417_);
v___x_446_ = lean_box(0);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
v___x_447_ = lean_apply_6(v___f_420_, v___x_446_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, lean_box(0));
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(lean_object* v___x_448_, lean_object* v_projName_449_, lean_object* v_n_450_, lean_object* v_ref_451_, lean_object* v___f_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v___x_17052__boxed_458_; lean_object* v_res_459_; 
v___x_17052__boxed_458_ = lean_unbox(v___x_448_);
v_res_459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_17052__boxed_458_, v_projName_449_, v_n_450_, v_ref_451_, v___f_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_ref_451_);
return v_res_459_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_460_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
v___x_466_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
lean_ctor_set(v___x_466_, 4, v___x_465_);
lean_ctor_set(v___x_466_, 5, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(lean_object* v_declName_467_, uint8_t v_s_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v_env_473_; lean_object* v_nextMacroScope_474_; lean_object* v_ngen_475_; lean_object* v_auxDeclNGen_476_; lean_object* v_traceState_477_; lean_object* v_recordedDeps_478_; lean_object* v_messages_479_; lean_object* v_infoState_480_; lean_object* v_snapshotTasks_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_510_; 
v___x_472_ = lean_st_ref_take(v___y_470_);
v_env_473_ = lean_ctor_get(v___x_472_, 0);
v_nextMacroScope_474_ = lean_ctor_get(v___x_472_, 1);
v_ngen_475_ = lean_ctor_get(v___x_472_, 2);
v_auxDeclNGen_476_ = lean_ctor_get(v___x_472_, 3);
v_traceState_477_ = lean_ctor_get(v___x_472_, 4);
v_recordedDeps_478_ = lean_ctor_get(v___x_472_, 6);
v_messages_479_ = lean_ctor_get(v___x_472_, 7);
v_infoState_480_ = lean_ctor_get(v___x_472_, 8);
v_snapshotTasks_481_ = lean_ctor_get(v___x_472_, 9);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v___x_472_, 5);
lean_dec(v_unused_511_);
v___x_483_ = v___x_472_;
v_isShared_484_ = v_isSharedCheck_510_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snapshotTasks_481_);
lean_inc(v_infoState_480_);
lean_inc(v_messages_479_);
lean_inc(v_recordedDeps_478_);
lean_inc(v_traceState_477_);
lean_inc(v_auxDeclNGen_476_);
lean_inc(v_ngen_475_);
lean_inc(v_nextMacroScope_474_);
lean_inc(v_env_473_);
lean_dec(v___x_472_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_510_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_485_ = 0;
v___x_486_ = lean_box(0);
v___x_487_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_473_, v_declName_467_, v_s_468_, v___x_485_, v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 5, v___x_488_);
lean_ctor_set(v___x_483_, 0, v___x_487_);
v___x_490_ = v___x_483_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_nextMacroScope_474_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_ngen_475_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_auxDeclNGen_476_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v_traceState_477_);
lean_ctor_set(v_reuseFailAlloc_509_, 5, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_509_, 6, v_recordedDeps_478_);
lean_ctor_set(v_reuseFailAlloc_509_, 7, v_messages_479_);
lean_ctor_set(v_reuseFailAlloc_509_, 8, v_infoState_480_);
lean_ctor_set(v_reuseFailAlloc_509_, 9, v_snapshotTasks_481_);
v___x_490_ = v_reuseFailAlloc_509_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_zetaDeltaFVarIds_494_; lean_object* v_postponed_495_; lean_object* v_diag_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_507_; 
v___x_491_ = lean_st_ref_put(v___y_470_, v___x_490_);
v___x_492_ = lean_st_ref_take(v___y_469_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
v_zetaDeltaFVarIds_494_ = lean_ctor_get(v___x_492_, 2);
v_postponed_495_ = lean_ctor_get(v___x_492_, 3);
v_diag_496_ = lean_ctor_get(v___x_492_, 4);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_492_, 1);
lean_dec(v_unused_508_);
v___x_498_ = v___x_492_;
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_diag_496_);
lean_inc(v_postponed_495_);
lean_inc(v_zetaDeltaFVarIds_494_);
lean_inc(v_mctx_493_);
lean_dec(v___x_492_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_mctx_493_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_zetaDeltaFVarIds_494_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_postponed_495_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_diag_496_);
v___x_503_ = v_reuseFailAlloc_506_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_st_ref_put(v___y_469_, v___x_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_500_);
return v___x_505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(lean_object* v_declName_512_, lean_object* v_s_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v_s_boxed_517_; lean_object* v_res_518_; 
v_s_boxed_517_ = lean_unbox(v_s_513_);
v_res_518_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_512_, v_s_boxed_517_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec(v___y_514_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_declName_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_525_ = 0;
v___x_526_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_519_, v___x_525_, v___y_521_, v___y_523_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_declName_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_declName_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(lean_object* v___x_543_, lean_object* v_projName_544_, lean_object* v___x_545_, lean_object* v_a_546_, uint8_t v_instImplicit_547_, lean_object* v___x_548_, lean_object* v_params_549_, lean_object* v_self_550_, lean_object* v_b_551_, uint8_t v___x_552_, lean_object* v_a_553_, lean_object* v___x_554_, lean_object* v_paramInfoOverrides_555_, lean_object* v_n_556_, lean_object* v_ref_557_, lean_object* v___x_558_, uint8_t v_a_559_, lean_object* v_____r_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; uint8_t v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; uint8_t v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = l_List_lengthTR___redArg(v_paramInfoOverrides_555_);
v___x_729_ = lean_array_get_size(v_params_549_);
v___x_730_ = lean_nat_dec_le(v___x_728_, v___x_729_);
lean_dec(v___x_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
lean_inc(v_projName_544_);
v___x_732_ = l_Lean_MessageData_ofName(v_projName_544_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v_n_556_);
v___x_736_ = l_Lean_MessageData_ofConstName(v_n_556_, v___x_730_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_557_, v___x_739_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref_known(v___x_740_, 1);
goto v___jp_689_;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_558_);
lean_dec(v_n_556_);
lean_dec_ref(v_a_553_);
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
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
v___jp_566_:
{
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v_nextMacroScope_571_; lean_object* v_ngen_572_; lean_object* v_auxDeclNGen_573_; lean_object* v_traceState_574_; lean_object* v_recordedDeps_575_; lean_object* v_messages_576_; lean_object* v_infoState_577_; lean_object* v_snapshotTasks_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_610_; 
v___x_569_ = lean_st_ref_take(v___y_568_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
v_nextMacroScope_571_ = lean_ctor_get(v___x_569_, 1);
v_ngen_572_ = lean_ctor_get(v___x_569_, 2);
v_auxDeclNGen_573_ = lean_ctor_get(v___x_569_, 3);
v_traceState_574_ = lean_ctor_get(v___x_569_, 4);
v_recordedDeps_575_ = lean_ctor_get(v___x_569_, 6);
v_messages_576_ = lean_ctor_get(v___x_569_, 7);
v_infoState_577_ = lean_ctor_get(v___x_569_, 8);
v_snapshotTasks_578_ = lean_ctor_get(v___x_569_, 9);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_569_, 5);
lean_dec(v_unused_611_);
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_610_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_snapshotTasks_578_);
lean_inc(v_infoState_577_);
lean_inc(v_messages_576_);
lean_inc(v_recordedDeps_575_);
lean_inc(v_traceState_574_);
lean_inc(v_auxDeclNGen_573_);
lean_inc(v_ngen_572_);
lean_inc(v_nextMacroScope_571_);
lean_inc(v_env_570_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_610_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_name_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v_name_582_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_name_582_);
lean_dec_ref(v___x_543_);
lean_inc(v_projName_544_);
v___x_583_ = l_Lean_addProjectionFnInfo(v_env_570_, v_projName_544_, v_name_582_, v___x_545_, v_a_546_, v_instImplicit_547_);
v___x_584_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 5, v___x_584_);
lean_ctor_set(v___x_580_, 0, v___x_583_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_nextMacroScope_571_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_ngen_572_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_auxDeclNGen_573_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_traceState_574_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_recordedDeps_575_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_messages_576_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_infoState_577_);
lean_ctor_set(v_reuseFailAlloc_609_, 9, v_snapshotTasks_578_);
v___x_586_ = v_reuseFailAlloc_609_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_mctx_589_; lean_object* v_zetaDeltaFVarIds_590_; lean_object* v_postponed_591_; lean_object* v_diag_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_607_; 
v___x_587_ = lean_st_ref_put(v___y_568_, v___x_586_);
v___x_588_ = lean_st_ref_take(v___y_567_);
v_mctx_589_ = lean_ctor_get(v___x_588_, 0);
v_zetaDeltaFVarIds_590_ = lean_ctor_get(v___x_588_, 2);
v_postponed_591_ = lean_ctor_get(v___x_588_, 3);
v_diag_592_ = lean_ctor_get(v___x_588_, 4);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_588_, 1);
lean_dec(v_unused_608_);
v___x_594_ = v___x_588_;
v_isShared_595_ = v_isSharedCheck_607_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_diag_592_);
lean_inc(v_postponed_591_);
lean_inc(v_zetaDeltaFVarIds_590_);
lean_inc(v_mctx_589_);
lean_dec(v___x_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_607_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_mctx_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_zetaDeltaFVarIds_590_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_postponed_591_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_diag_592_);
v___x_598_ = v_reuseFailAlloc_606_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_599_ = lean_st_ref_put(v___y_567_, v___x_598_);
v___x_600_ = l_Lean_Expr_const___override(v_projName_544_, v___x_548_);
v___x_601_ = l_Lean_mkAppN(v___x_600_, v_params_549_);
v___x_602_ = l_Lean_Expr_app___override(v___x_601_, v_self_550_);
v___x_603_ = l_Lean_Expr_bindingBody_x21(v_b_551_);
v___x_604_ = lean_expr_instantiate1(v___x_603_, v___x_602_);
lean_dec_ref(v___x_602_);
lean_dec_ref(v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
}
}
v___jp_612_:
{
if (lean_obj_tag(v___y_615_) == 0)
{
lean_dec_ref_known(v___y_615_, 1);
v___y_567_ = v___y_613_;
v___y_568_ = v___y_614_;
goto v___jp_566_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
v_a_616_ = lean_ctor_get(v___y_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___y_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___y_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___y_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
v___jp_624_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = lean_box(0);
lean_inc(v_projName_544_);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v_projName_544_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_633_, 0, v___y_629_);
lean_ctor_set(v___x_633_, 1, v___y_630_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3, v___x_552_);
v___x_634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___x_635_ = l_Lean_addDecl(v___x_634_, v___y_625_, v___y_628_, v___y_627_);
lean_dec_ref(v___y_628_);
v___y_613_ = v___y_626_;
v___y_614_ = v___y_627_;
v___y_615_ = v___x_635_;
goto v___jp_612_;
}
v___jp_636_:
{
uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v_toCold_645_; lean_object* v_currRecDepth_646_; lean_object* v_ref_647_; uint16_t v_optionFlags_648_; uint8_t v_suppressElabErrors_649_; uint8_t v_isRecordingDeps_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_ref_655_; lean_object* v___x_656_; 
v___x_643_ = 0;
lean_inc_ref(v_a_553_);
v___x_644_ = l_Lean_LocalContext_mkForall(v_a_553_, v___x_554_, v___y_638_, v___x_552_, v___x_643_);
lean_dec_ref(v___y_638_);
v_toCold_645_ = lean_ctor_get(v___y_641_, 0);
v_currRecDepth_646_ = lean_ctor_get(v___y_641_, 1);
v_ref_647_ = lean_ctor_get(v___y_641_, 2);
v_optionFlags_648_ = lean_ctor_get_uint16(v___y_641_, sizeof(void*)*3);
v_suppressElabErrors_649_ = lean_ctor_get_uint8(v___y_641_, sizeof(void*)*3 + 2);
v_isRecordingDeps_650_ = lean_ctor_get_uint8(v___y_641_, sizeof(void*)*3 + 3);
v___x_651_ = l_Lean_Expr_inferImplicit(v___x_644_, v___x_545_, v___x_552_);
v___x_652_ = l_Lean_Expr_updateForallBinderInfos(v___x_651_, v_paramInfoOverrides_555_);
lean_inc_ref(v_self_550_);
lean_inc(v_a_546_);
v___x_653_ = l_Lean_Expr_proj___override(v_n_556_, v_a_546_, v_self_550_);
v___x_654_ = l_Lean_LocalContext_mkLambda(v_a_553_, v___x_554_, v___x_653_, v___x_552_, v___x_643_);
lean_dec_ref(v___x_653_);
v_ref_655_ = l_Lean_replaceRef(v_ref_557_, v_ref_647_);
lean_inc(v_currRecDepth_646_);
lean_inc_ref(v_toCold_645_);
v___x_656_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_656_, 0, v_toCold_645_);
lean_ctor_set(v___x_656_, 1, v_currRecDepth_646_);
lean_ctor_set(v___x_656_, 2, v_ref_655_);
lean_ctor_set_uint16(v___x_656_, sizeof(void*)*3, v_optionFlags_648_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 2, v_suppressElabErrors_649_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*3 + 3, v_isRecordingDeps_650_);
if (v___y_637_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(1);
lean_inc(v_projName_544_);
v___x_658_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_544_, v___x_558_, v___x_652_, v___x_654_, v___x_657_, v___y_642_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v_a_659_);
v___x_661_ = l_Lean_addDecl(v___x_660_, v___x_643_, v___x_656_, v___y_642_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
if (v_instImplicit_547_ == 0)
{
lean_object* v___x_662_; 
lean_inc(v_projName_544_);
v___x_662_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_544_, v___y_639_, v___y_640_, v___x_656_, v___y_642_);
lean_dec_ref_known(v___x_656_, 3);
v___y_613_ = v___y_640_;
v___y_614_ = v___y_642_;
v___y_615_ = v___x_662_;
goto v___jp_612_;
}
else
{
lean_dec_ref_known(v___x_656_, 3);
v___y_567_ = v___y_640_;
v___y_568_ = v___y_642_;
goto v___jp_566_;
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref_known(v___x_656_, 3);
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
v_a_663_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_661_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref_known(v___x_656_, 3);
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_658_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_658_);
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
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_env_681_; uint8_t v___x_682_; 
lean_inc_ref(v___x_652_);
lean_inc(v_projName_544_);
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v_projName_544_);
lean_ctor_set(v___x_679_, 1, v___x_558_);
lean_ctor_set(v___x_679_, 2, v___x_652_);
v___x_680_ = lean_st_ref_get(v___y_642_);
v_env_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref_n(v_env_681_, 2);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_Environment_hasUnsafe(v_env_681_, v___x_652_);
lean_dec_ref(v___x_652_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Environment_hasUnsafe(v_env_681_, v___x_654_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_684_ = lean_box(0);
lean_inc(v_projName_544_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v_projName_544_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_679_);
lean_ctor_set(v___x_686_, 1, v___x_654_);
lean_ctor_set(v___x_686_, 2, v___x_685_);
v___x_687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = l_Lean_addDecl(v___x_687_, v___x_643_, v___x_656_, v___y_642_);
lean_dec_ref_known(v___x_656_, 3);
v___y_613_ = v___y_640_;
v___y_614_ = v___y_642_;
v___y_615_ = v___x_688_;
goto v___jp_612_;
}
else
{
v___y_625_ = v___x_643_;
v___y_626_ = v___y_640_;
v___y_627_ = v___y_642_;
v___y_628_ = v___x_656_;
v___y_629_ = v___x_679_;
v___y_630_ = v___x_654_;
goto v___jp_624_;
}
}
else
{
lean_dec_ref(v_env_681_);
v___y_625_ = v___x_643_;
v___y_626_ = v___y_640_;
v___y_627_ = v___y_642_;
v___y_628_ = v___x_656_;
v___y_629_ = v___x_679_;
v___y_630_ = v___x_654_;
goto v___jp_624_;
}
}
}
v___jp_689_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_Expr_bindingDomain_x21(v_b_551_);
v___x_691_ = lean_expr_consume_type_annotations(v___x_690_);
lean_inc_ref(v___x_691_);
v___x_692_ = l_Lean_Meta_isProp(v___x_691_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_692_) == 0)
{
if (v_a_559_ == 0)
{
lean_object* v_a_693_; uint8_t v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_unbox(v_a_693_);
lean_dec(v_a_693_);
v___y_637_ = v___x_694_;
v___y_638_ = v___x_691_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
goto v___jp_636_;
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
lean_inc(v_projName_544_);
v___x_698_ = l_Lean_MessageData_ofName(v_projName_544_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_unbox(v_a_695_);
lean_inc(v_n_556_);
v___x_703_ = l_Lean_MessageData_ofConstName(v_n_556_, v___x_702_);
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
v___x_709_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_557_, v___x_708_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_709_) == 0)
{
uint8_t v___x_710_; 
lean_dec_ref_known(v___x_709_, 1);
v___x_710_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
v___y_637_ = v___x_710_;
v___y_638_ = v___x_691_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
goto v___jp_636_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_695_);
lean_dec_ref(v___x_691_);
lean_dec(v___x_558_);
lean_dec(v_n_556_);
lean_dec_ref(v_a_553_);
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
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
v___y_637_ = v___x_719_;
v___y_638_ = v___x_691_;
v___y_639_ = v___y_561_;
v___y_640_ = v___y_562_;
v___y_641_ = v___y_563_;
v___y_642_ = v___y_564_;
goto v___jp_636_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___x_691_);
lean_dec(v___x_558_);
lean_dec(v_n_556_);
lean_dec_ref(v_a_553_);
lean_dec_ref(v_self_550_);
lean_dec(v___x_548_);
lean_dec(v_a_546_);
lean_dec(v___x_545_);
lean_dec(v_projName_544_);
lean_dec_ref(v___x_543_);
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
uint8_t v_instImplicit_boxed_772_; uint8_t v___x_17291__boxed_773_; uint8_t v_a_17297__boxed_774_; lean_object* v_res_775_; 
v_instImplicit_boxed_772_ = lean_unbox(v_instImplicit_753_);
v___x_17291__boxed_773_ = lean_unbox(v___x_758_);
v_a_17297__boxed_774_ = lean_unbox(v_a_765_);
v_res_775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_749_, v_projName_750_, v___x_751_, v_a_752_, v_instImplicit_boxed_772_, v___x_754_, v_params_755_, v_self_756_, v_b_757_, v___x_17291__boxed_773_, v_a_759_, v___x_760_, v_paramInfoOverrides_761_, v_n_762_, v_ref_763_, v___x_764_, v_a_17297__boxed_774_, v_____r_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
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
lean_object* v___x_783_; lean_object* v_env_784_; lean_object* v_nextMacroScope_785_; lean_object* v_ngen_786_; lean_object* v_auxDeclNGen_787_; lean_object* v_traceState_788_; lean_object* v_recordedDeps_789_; lean_object* v_messages_790_; lean_object* v_infoState_791_; lean_object* v_snapshotTasks_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_817_; 
v___x_783_ = lean_st_ref_take(v___y_776_);
v_env_784_ = lean_ctor_get(v___x_783_, 0);
v_nextMacroScope_785_ = lean_ctor_get(v___x_783_, 1);
v_ngen_786_ = lean_ctor_get(v___x_783_, 2);
v_auxDeclNGen_787_ = lean_ctor_get(v___x_783_, 3);
v_traceState_788_ = lean_ctor_get(v___x_783_, 4);
v_recordedDeps_789_ = lean_ctor_get(v___x_783_, 6);
v_messages_790_ = lean_ctor_get(v___x_783_, 7);
v_infoState_791_ = lean_ctor_get(v___x_783_, 8);
v_snapshotTasks_792_ = lean_ctor_get(v___x_783_, 9);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_783_, 5);
lean_dec(v_unused_818_);
v___x_794_ = v___x_783_;
v_isShared_795_ = v_isSharedCheck_817_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_snapshotTasks_792_);
lean_inc(v_infoState_791_);
lean_inc(v_messages_790_);
lean_inc(v_recordedDeps_789_);
lean_inc(v_traceState_788_);
lean_inc(v_auxDeclNGen_787_);
lean_inc(v_ngen_786_);
lean_inc(v_nextMacroScope_785_);
lean_inc(v_env_784_);
lean_dec(v___x_783_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_817_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_Environment_setExporting(v_env_784_, v_isExporting_777_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 5, v___x_778_);
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_nextMacroScope_785_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_ngen_786_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_auxDeclNGen_787_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_traceState_788_);
lean_ctor_set(v_reuseFailAlloc_816_, 5, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_816_, 6, v_recordedDeps_789_);
lean_ctor_set(v_reuseFailAlloc_816_, 7, v_messages_790_);
lean_ctor_set(v_reuseFailAlloc_816_, 8, v_infoState_791_);
lean_ctor_set(v_reuseFailAlloc_816_, 9, v_snapshotTasks_792_);
v___x_798_ = v_reuseFailAlloc_816_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v_mctx_801_; lean_object* v_zetaDeltaFVarIds_802_; lean_object* v_postponed_803_; lean_object* v_diag_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
v___x_799_ = lean_st_ref_put(v___y_776_, v___x_798_);
v___x_800_ = lean_st_ref_take(v___y_779_);
v_mctx_801_ = lean_ctor_get(v___x_800_, 0);
v_zetaDeltaFVarIds_802_ = lean_ctor_get(v___x_800_, 2);
v_postponed_803_ = lean_ctor_get(v___x_800_, 3);
v_diag_804_ = lean_ctor_get(v___x_800_, 4);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_800_, 1);
lean_dec(v_unused_815_);
v___x_806_ = v___x_800_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_diag_804_);
lean_inc(v_postponed_803_);
lean_inc(v_zetaDeltaFVarIds_802_);
lean_inc(v_mctx_801_);
lean_dec(v___x_800_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_780_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_mctx_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_zetaDeltaFVarIds_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_postponed_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_diag_804_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_st_ref_put(v___y_779_, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_808_);
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___y_819_, lean_object* v_isExporting_820_, lean_object* v___x_821_, lean_object* v___y_822_, lean_object* v___x_823_, lean_object* v_a_x3f_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_isExporting_boxed_826_; lean_object* v_res_827_; 
v_isExporting_boxed_826_ = lean_unbox(v_isExporting_820_);
v_res_827_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_819_, v_isExporting_boxed_826_, v___x_821_, v___y_822_, v___x_823_, v_a_x3f_824_);
lean_dec(v_a_x3f_824_);
lean_dec(v___y_822_);
lean_dec(v___y_819_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(lean_object* v_x_828_, uint8_t v_isExporting_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; lean_object* v___x_837_; uint8_t v_isModule_838_; 
v___x_835_ = lean_st_ref_get(v___y_833_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_env_836_);
lean_dec(v___x_835_);
v___x_837_ = l_Lean_Environment_header(v_env_836_);
v_isModule_838_ = lean_ctor_get_uint8(v___x_837_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_837_);
if (v_isModule_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v_env_836_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
v___x_839_ = lean_apply_5(v_x_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
return v___x_839_;
}
else
{
uint8_t v_isExporting_840_; 
v_isExporting_840_ = lean_ctor_get_uint8(v_env_836_, sizeof(void*)*13);
lean_dec_ref(v_env_836_);
if (v_isExporting_829_ == 0)
{
if (v_isExporting_840_ == 0)
{
lean_object* v___x_907_; 
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
v___x_907_ = lean_apply_5(v_x_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
return v___x_907_;
}
else
{
goto v___jp_841_;
}
}
else
{
if (v_isExporting_840_ == 0)
{
goto v___jp_841_;
}
else
{
lean_object* v___x_908_; 
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
v___x_908_ = lean_apply_5(v_x_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
return v___x_908_;
}
}
v___jp_841_:
{
lean_object* v___x_842_; lean_object* v_env_843_; lean_object* v_nextMacroScope_844_; lean_object* v_ngen_845_; lean_object* v_auxDeclNGen_846_; lean_object* v_traceState_847_; lean_object* v_recordedDeps_848_; lean_object* v_messages_849_; lean_object* v_infoState_850_; lean_object* v_snapshotTasks_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_905_; 
v___x_842_ = lean_st_ref_take(v___y_833_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
v_nextMacroScope_844_ = lean_ctor_get(v___x_842_, 1);
v_ngen_845_ = lean_ctor_get(v___x_842_, 2);
v_auxDeclNGen_846_ = lean_ctor_get(v___x_842_, 3);
v_traceState_847_ = lean_ctor_get(v___x_842_, 4);
v_recordedDeps_848_ = lean_ctor_get(v___x_842_, 6);
v_messages_849_ = lean_ctor_get(v___x_842_, 7);
v_infoState_850_ = lean_ctor_get(v___x_842_, 8);
v_snapshotTasks_851_ = lean_ctor_get(v___x_842_, 9);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_842_, 5);
lean_dec(v_unused_906_);
v___x_853_ = v___x_842_;
v_isShared_854_ = v_isSharedCheck_905_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snapshotTasks_851_);
lean_inc(v_infoState_850_);
lean_inc(v_messages_849_);
lean_inc(v_recordedDeps_848_);
lean_inc(v_traceState_847_);
lean_inc(v_auxDeclNGen_846_);
lean_inc(v_ngen_845_);
lean_inc(v_nextMacroScope_844_);
lean_inc(v_env_843_);
lean_dec(v___x_842_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_905_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = l_Lean_Environment_setExporting(v_env_843_, v_isExporting_829_);
v___x_856_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 5, v___x_856_);
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_nextMacroScope_844_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_ngen_845_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_auxDeclNGen_846_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_traceState_847_);
lean_ctor_set(v_reuseFailAlloc_904_, 5, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_904_, 6, v_recordedDeps_848_);
lean_ctor_set(v_reuseFailAlloc_904_, 7, v_messages_849_);
lean_ctor_set(v_reuseFailAlloc_904_, 8, v_infoState_850_);
lean_ctor_set(v_reuseFailAlloc_904_, 9, v_snapshotTasks_851_);
v___x_858_ = v_reuseFailAlloc_904_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_mctx_861_; lean_object* v_zetaDeltaFVarIds_862_; lean_object* v_postponed_863_; lean_object* v_diag_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_902_; 
v___x_859_ = lean_st_ref_put(v___y_833_, v___x_858_);
v___x_860_ = lean_st_ref_take(v___y_831_);
v_mctx_861_ = lean_ctor_get(v___x_860_, 0);
v_zetaDeltaFVarIds_862_ = lean_ctor_get(v___x_860_, 2);
v_postponed_863_ = lean_ctor_get(v___x_860_, 3);
v_diag_864_ = lean_ctor_get(v___x_860_, 4);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_860_, 1);
lean_dec(v_unused_903_);
v___x_866_ = v___x_860_;
v_isShared_867_ = v_isSharedCheck_902_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_diag_864_);
lean_inc(v_postponed_863_);
lean_inc(v_zetaDeltaFVarIds_862_);
lean_inc(v_mctx_861_);
lean_dec(v___x_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_902_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_mctx_861_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_zetaDeltaFVarIds_862_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_postponed_863_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_diag_864_);
v___x_870_ = v_reuseFailAlloc_901_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; lean_object* v_r_872_; 
v___x_871_ = lean_st_ref_put(v___y_831_, v___x_870_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
v_r_872_ = lean_apply_5(v_x_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
if (lean_obj_tag(v_r_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_889_; 
v_a_873_ = lean_ctor_get(v_r_872_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_r_872_);
if (v_isSharedCheck_889_ == 0)
{
v___x_875_ = v_r_872_;
v_isShared_876_ = v_isSharedCheck_889_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_r_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_889_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
lean_inc(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_888_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v___x_879_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_833_, v_isExporting_840_, v___x_856_, v___y_831_, v___x_868_, v___x_878_);
lean_dec_ref(v___x_878_);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_879_, 0);
lean_dec(v_unused_887_);
v___x_881_ = v___x_879_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_879_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_a_873_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_873_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_890_ = lean_ctor_get(v_r_872_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v_r_872_, 1);
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_833_, v_isExporting_840_, v___x_856_, v___y_831_, v___x_868_, v___x_891_);
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
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v_a_890_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_890_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(lean_object* v_x_909_, lean_object* v_isExporting_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v_isExporting_boxed_916_; lean_object* v_res_917_; 
v_isExporting_boxed_916_ = lean_unbox(v_isExporting_910_);
v_res_917_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_909_, v_isExporting_boxed_916_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_x_918_, uint8_t v_when_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
if (v_when_919_ == 0)
{
lean_object* v___x_925_; 
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
v___x_925_ = lean_apply_5(v_x_918_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, lean_box(0));
return v___x_925_;
}
else
{
uint8_t v___x_926_; lean_object* v___x_927_; 
v___x_926_ = 0;
v___x_927_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_918_, v___x_926_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_x_928_, lean_object* v_when_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
uint8_t v_when_boxed_935_; lean_object* v_res_936_; 
v_when_boxed_935_ = lean_unbox(v_when_929_);
v_res_936_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_928_, v_when_boxed_935_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_upperBound_937_, lean_object* v_projDecls_938_, lean_object* v___x_939_, lean_object* v___x_940_, uint8_t v_instImplicit_941_, lean_object* v___x_942_, lean_object* v_params_943_, lean_object* v_self_944_, lean_object* v_a_945_, lean_object* v___x_946_, lean_object* v_n_947_, lean_object* v___x_948_, uint8_t v_a_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_lt(v_a_950_, v_upperBound_937_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_dec(v_a_950_);
lean_dec(v___x_948_);
lean_dec(v_n_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_self_944_);
lean_dec_ref(v_params_943_);
lean_dec(v___x_942_);
lean_dec(v___x_940_);
lean_dec_ref(v___x_939_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_951_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v_ref_960_; lean_object* v_projName_961_; lean_object* v_paramInfoOverrides_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___f_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___y_969_; uint8_t v___x_970_; lean_object* v___x_971_; 
v___x_959_ = lean_array_fget_borrowed(v_projDecls_938_, v_a_950_);
v_ref_960_ = lean_ctor_get(v___x_959_, 0);
v_projName_961_ = lean_ctor_get(v___x_959_, 1);
v_paramInfoOverrides_962_ = lean_ctor_get(v___x_959_, 2);
v___x_963_ = lean_box(v_instImplicit_941_);
v___x_964_ = lean_box(v___x_957_);
v___x_965_ = lean_box(v_a_949_);
lean_inc(v___x_948_);
lean_inc_n(v_ref_960_, 2);
lean_inc_n(v_n_947_, 2);
lean_inc(v_paramInfoOverrides_962_);
lean_inc_ref(v___x_946_);
lean_inc_ref(v_a_945_);
lean_inc_ref(v_b_951_);
lean_inc_ref(v_self_944_);
lean_inc_ref(v_params_943_);
lean_inc(v___x_942_);
lean_inc(v_a_950_);
lean_inc(v___x_940_);
lean_inc_n(v_projName_961_, 2);
lean_inc_ref(v___x_939_);
v___f_966_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_966_, 0, v___x_939_);
lean_closure_set(v___f_966_, 1, v_projName_961_);
lean_closure_set(v___f_966_, 2, v___x_940_);
lean_closure_set(v___f_966_, 3, v_a_950_);
lean_closure_set(v___f_966_, 4, v___x_963_);
lean_closure_set(v___f_966_, 5, v___x_942_);
lean_closure_set(v___f_966_, 6, v_params_943_);
lean_closure_set(v___f_966_, 7, v_self_944_);
lean_closure_set(v___f_966_, 8, v_b_951_);
lean_closure_set(v___f_966_, 9, v___x_964_);
lean_closure_set(v___f_966_, 10, v_a_945_);
lean_closure_set(v___f_966_, 11, v___x_946_);
lean_closure_set(v___f_966_, 12, v_paramInfoOverrides_962_);
lean_closure_set(v___f_966_, 13, v_n_947_);
lean_closure_set(v___f_966_, 14, v_ref_960_);
lean_closure_set(v___f_966_, 15, v___x_948_);
lean_closure_set(v___f_966_, 16, v___x_965_);
v___x_967_ = l_Lean_Expr_isForall(v_b_951_);
lean_dec_ref(v_b_951_);
v___x_968_ = lean_box(v___x_967_);
v___y_969_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_969_, 0, v___x_968_);
lean_closure_set(v___y_969_, 1, v_projName_961_);
lean_closure_set(v___y_969_, 2, v_n_947_);
lean_closure_set(v___y_969_, 3, v_ref_960_);
lean_closure_set(v___y_969_, 4, v___f_966_);
v___x_970_ = l_Lean_isPrivateName(v_projName_961_);
v___x_971_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v___y_969_, v___x_970_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_add(v_a_950_, v___x_973_);
lean_dec(v_a_950_);
v_a_950_ = v___x_974_;
v_b_951_ = v_a_972_;
goto _start;
}
else
{
lean_dec(v_a_950_);
lean_dec(v___x_948_);
lean_dec(v_n_947_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v_a_945_);
lean_dec_ref(v_self_944_);
lean_dec_ref(v_params_943_);
lean_dec(v___x_942_);
lean_dec(v___x_940_);
lean_dec_ref(v___x_939_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_976_ = _args[0];
lean_object* v_projDecls_977_ = _args[1];
lean_object* v___x_978_ = _args[2];
lean_object* v___x_979_ = _args[3];
lean_object* v_instImplicit_980_ = _args[4];
lean_object* v___x_981_ = _args[5];
lean_object* v_params_982_ = _args[6];
lean_object* v_self_983_ = _args[7];
lean_object* v_a_984_ = _args[8];
lean_object* v___x_985_ = _args[9];
lean_object* v_n_986_ = _args[10];
lean_object* v___x_987_ = _args[11];
lean_object* v_a_988_ = _args[12];
lean_object* v_a_989_ = _args[13];
lean_object* v_b_990_ = _args[14];
lean_object* v___y_991_ = _args[15];
lean_object* v___y_992_ = _args[16];
lean_object* v___y_993_ = _args[17];
lean_object* v___y_994_ = _args[18];
lean_object* v___y_995_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_996_; uint8_t v_a_17909__boxed_997_; lean_object* v_res_998_; 
v_instImplicit_boxed_996_ = lean_unbox(v_instImplicit_980_);
v_a_17909__boxed_997_ = lean_unbox(v_a_988_);
v_res_998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_976_, v_projDecls_977_, v___x_978_, v___x_979_, v_instImplicit_boxed_996_, v___x_981_, v_params_982_, v_self_983_, v_a_984_, v___x_985_, v_n_986_, v___x_987_, v_a_17909__boxed_997_, v_a_989_, v_b_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_projDecls_977_);
lean_dec(v_upperBound_976_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_999_, lean_object* v_as_1000_, size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_a_1009_; uint8_t v___x_1013_; 
v___x_1013_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_b_1003_);
return v___x_1014_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1015_ = lean_array_uget_borrowed(v_as_1000_, v_i_1002_);
v___x_1016_ = l_Lean_Expr_fvarId_x21(v_a_1015_);
lean_inc(v___x_1016_);
v___x_1017_ = l_Lean_FVarId_getDecl___redArg(v___x_1016_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; uint8_t v___x_1020_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l_Lean_LocalDecl_binderInfo(v_a_1018_);
v___x_1020_ = l_Lean_BinderInfo_isInstImplicit(v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = l_Lean_LocalDecl_type(v_a_1018_);
lean_dec(v_a_1018_);
v___x_1025_ = l_Lean_Expr_isOutParam(v___x_1024_);
lean_dec_ref(v___x_1024_);
if (v___x_1025_ == 0)
{
uint8_t v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = 0;
v___x_1027_ = l_Lean_LocalContext_setBinderInfo(v_b_1003_, v___x_1016_, v___x_1026_);
v_a_1009_ = v___x_1027_;
goto v___jp_1008_;
}
else
{
goto v___jp_1021_;
}
}
else
{
lean_dec(v_a_1018_);
goto v___jp_1021_;
}
v___jp_1021_:
{
if (v___x_1020_ == 0)
{
lean_dec(v___x_1016_);
v_a_1009_ = v_b_1003_;
goto v___jp_1008_;
}
else
{
if (v_instImplicit_999_ == 0)
{
lean_dec(v___x_1016_);
v_a_1009_ = v_b_1003_;
goto v___jp_1008_;
}
else
{
uint8_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = 1;
v___x_1023_ = l_Lean_LocalContext_setBinderInfo(v_b_1003_, v___x_1016_, v___x_1022_);
v_a_1009_ = v___x_1023_;
goto v___jp_1008_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___x_1016_);
lean_dec_ref(v_b_1003_);
v_a_1028_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1017_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1017_);
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
v___jp_1008_:
{
size_t v___x_1010_; size_t v___x_1011_; 
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1002_, v___x_1010_);
v_i_1002_ = v___x_1011_;
v_b_1003_ = v_a_1009_;
goto _start;
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
uint8_t v_instImplicit_boxed_1115_; uint8_t v_a_18047__boxed_1116_; lean_object* v_res_1117_; 
v_instImplicit_boxed_1115_ = lean_unbox(v_instImplicit_1100_);
v_a_18047__boxed_1116_ = lean_unbox(v_a_1107_);
v_res_1117_ = l_Lean_Meta_mkProjections___lam__0(v_params_1099_, v_instImplicit_boxed_1115_, v_projDecls_1101_, v_toConstantVal_1102_, v_numParams_1103_, v___x_1104_, v_n_1105_, v_levelParams_1106_, v_a_18047__boxed_1116_, v_ctorType_1108_, v_self_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
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
v___x_1152_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1150_, v___y_1149_, v___y_1145_, v___y_1146_, v___x_1151_, v___y_1143_, v___y_1148_, v___y_1147_, v___y_1144_);
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
v___y_1143_ = v___y_1137_;
v___y_1144_ = v___y_1140_;
v___y_1145_ = v___x_1158_;
v___y_1146_ = v___f_1155_;
v___y_1147_ = v___y_1139_;
v___y_1148_ = v___y_1138_;
v___y_1149_ = v___x_1159_;
goto v___jp_1142_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 3;
v___y_1143_ = v___y_1137_;
v___y_1144_ = v___y_1140_;
v___y_1145_ = v___x_1158_;
v___y_1146_ = v___f_1155_;
v___y_1147_ = v___y_1139_;
v___y_1148_ = v___y_1138_;
v___y_1149_ = v___x_1160_;
goto v___jp_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1169_, lean_object* v_projDecls_1170_, lean_object* v_toConstantVal_1171_, lean_object* v_numParams_1172_, lean_object* v___x_1173_, lean_object* v_n_1174_, lean_object* v_levelParams_1175_, lean_object* v_a_1176_, lean_object* v_params_1177_, lean_object* v_ctorType_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_instImplicit_boxed_1184_; uint8_t v_a_18151__boxed_1185_; lean_object* v_res_1186_; 
v_instImplicit_boxed_1184_ = lean_unbox(v_instImplicit_1169_);
v_a_18151__boxed_1185_ = lean_unbox(v_a_1176_);
v_res_1186_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1184_, v_projDecls_1170_, v_toConstantVal_1171_, v_numParams_1172_, v___x_1173_, v_n_1174_, v_levelParams_1175_, v_a_18151__boxed_1185_, v_params_1177_, v_ctorType_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
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
v___x_1201_ = l_instMonadEIO___redArg();
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
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_13120__overap_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = l_instInhabitedOfMonad___redArg(v___x_1260_, v___x_1261_);
v___x_13120__overap_1263_ = lean_panic_fn_borrowed(v___x_1262_, v_msg_1206_);
lean_dec(v___x_1262_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
v___x_1264_ = lean_apply_5(v___x_13120__overap_1263_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, lean_box(0));
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
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(32u);
v___x_1473_ = lean_mk_empty_array_with_capacity(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1475_ = ((size_t)5ULL);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_unsigned_to_nat(32u);
v___x_1478_ = lean_mk_empty_array_with_capacity(v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1480_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___x_1478_);
lean_ctor_set(v___x_1480_, 2, v___x_1476_);
lean_ctor_set(v___x_1480_, 3, v___x_1476_);
lean_ctor_set_usize(v___x_1480_, 4, v___x_1475_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1481_ = lean_box(1);
v___x_1482_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1483_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
lean_ctor_set(v___x_1484_, 2, v___x_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1487_, lean_object* v_projDecls_1488_, uint8_t v_instImplicit_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_box(v_instImplicit_1489_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1497_, 0, v_n_1487_);
lean_closure_set(v___f_1497_, 1, v___x_1495_);
lean_closure_set(v___f_1497_, 2, v___x_1496_);
lean_closure_set(v___f_1497_, 3, v_projDecls_1488_);
v___x_1498_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1499_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1500_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1498_, v___x_1499_, v___f_1497_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1501_, lean_object* v_projDecls_1502_, lean_object* v_instImplicit_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
uint8_t v_instImplicit_boxed_1509_; lean_object* v_res_1510_; 
v_instImplicit_boxed_1509_ = lean_unbox(v_instImplicit_1503_);
v_res_1510_ = l_Lean_Meta_mkProjections(v_n_1501_, v_projDecls_1502_, v_instImplicit_boxed_1509_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1511_, lean_object* v_as_1512_, size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1511_, v_as_1512_, v_sz_1513_, v_i_1514_, v_b_1515_, v___y_1516_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1522_, lean_object* v_as_1523_, lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_instImplicit_boxed_1532_; size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_instImplicit_boxed_1532_ = lean_unbox(v_instImplicit_1522_);
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1532_, v_as_1523_, v_sz_boxed_1533_, v_i_boxed_1534_, v_b_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec_ref(v_as_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1536_, uint8_t v_s_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1536_, v_s_1537_, v___y_1539_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1544_, lean_object* v_s_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_s_boxed_1551_; lean_object* v_res_1552_; 
v_s_boxed_1551_ = lean_unbox(v_s_1545_);
v_res_1552_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1544_, v_s_boxed_1551_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1553_, lean_object* v_ref_1554_, lean_object* v_msg_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1554_, v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_ref_1563_, lean_object* v_msg_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1562_, v_ref_1563_, v_msg_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v_ref_1563_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1571_, lean_object* v_x_1572_, uint8_t v_isExporting_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1572_, v_isExporting_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_x_1581_, lean_object* v_isExporting_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_isExporting_boxed_1588_; lean_object* v_res_1589_; 
v_isExporting_boxed_1588_ = lean_unbox(v_isExporting_1582_);
v_res_1589_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1580_, v_x_1581_, v_isExporting_boxed_1588_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1590_, lean_object* v_x_1591_, uint8_t v_when_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1591_, v_when_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_x_1600_, lean_object* v_when_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v_when_boxed_1607_; lean_object* v_res_1608_; 
v_when_boxed_1607_ = lean_unbox(v_when_1601_);
v_res_1608_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1599_, v_x_1600_, v_when_boxed_1607_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1609_, lean_object* v_projDecls_1610_, lean_object* v___x_1611_, lean_object* v___x_1612_, uint8_t v_instImplicit_1613_, lean_object* v___x_1614_, lean_object* v_params_1615_, lean_object* v_self_1616_, lean_object* v_a_1617_, lean_object* v___x_1618_, lean_object* v_n_1619_, lean_object* v___x_1620_, uint8_t v_a_1621_, lean_object* v_inst_1622_, lean_object* v_R_1623_, lean_object* v_a_1624_, lean_object* v_b_1625_, lean_object* v_c_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1609_, v_projDecls_1610_, v___x_1611_, v___x_1612_, v_instImplicit_1613_, v___x_1614_, v_params_1615_, v_self_1616_, v_a_1617_, v___x_1618_, v_n_1619_, v___x_1620_, v_a_1621_, v_a_1624_, v_b_1625_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1633_ = _args[0];
lean_object* v_projDecls_1634_ = _args[1];
lean_object* v___x_1635_ = _args[2];
lean_object* v___x_1636_ = _args[3];
lean_object* v_instImplicit_1637_ = _args[4];
lean_object* v___x_1638_ = _args[5];
lean_object* v_params_1639_ = _args[6];
lean_object* v_self_1640_ = _args[7];
lean_object* v_a_1641_ = _args[8];
lean_object* v___x_1642_ = _args[9];
lean_object* v_n_1643_ = _args[10];
lean_object* v___x_1644_ = _args[11];
lean_object* v_a_1645_ = _args[12];
lean_object* v_inst_1646_ = _args[13];
lean_object* v_R_1647_ = _args[14];
lean_object* v_a_1648_ = _args[15];
lean_object* v_b_1649_ = _args[16];
lean_object* v_c_1650_ = _args[17];
lean_object* v___y_1651_ = _args[18];
lean_object* v___y_1652_ = _args[19];
lean_object* v___y_1653_ = _args[20];
lean_object* v___y_1654_ = _args[21];
lean_object* v___y_1655_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1656_; uint8_t v_a_18902__boxed_1657_; lean_object* v_res_1658_; 
v_instImplicit_boxed_1656_ = lean_unbox(v_instImplicit_1637_);
v_a_18902__boxed_1657_ = lean_unbox(v_a_1645_);
v_res_1658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1633_, v_projDecls_1634_, v___x_1635_, v___x_1636_, v_instImplicit_boxed_1656_, v___x_1638_, v_params_1639_, v_self_1640_, v_a_1641_, v___x_1642_, v_n_1643_, v___x_1644_, v_a_18902__boxed_1657_, v_inst_1646_, v_R_1647_, v_a_1648_, v_b_1649_, v_c_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v_projDecls_1634_);
lean_dec(v_upperBound_1633_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1659_, uint8_t v_allowLevelAssignments_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1660_, v_k_1659_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1666_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1666_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1683_, lean_object* v_allowLevelAssignments_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1690_; lean_object* v_res_1691_; 
v_allowLevelAssignments_boxed_1690_ = lean_unbox(v_allowLevelAssignments_1684_);
v_res_1691_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1683_, v_allowLevelAssignments_boxed_1690_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1692_, lean_object* v_k_1693_, uint8_t v_allowLevelAssignments_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1693_, v_allowLevelAssignments_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_k_1702_, lean_object* v_allowLevelAssignments_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1709_; lean_object* v_res_1710_; 
v_allowLevelAssignments_boxed_1709_ = lean_unbox(v_allowLevelAssignments_1703_);
v_res_1710_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1701_, v_k_1702_, v_allowLevelAssignments_boxed_1709_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1711_, size_t v_sz_1712_, size_t v_i_1713_, lean_object* v_b_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_usize_dec_lt(v_i_1713_, v_sz_1712_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v_b_1714_);
return v___x_1721_;
}
else
{
lean_object* v_snd_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1777_; 
v_snd_1722_ = lean_ctor_get(v_b_1714_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_b_1714_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v_b_1714_, 0);
lean_dec(v_unused_1778_);
v___x_1724_ = v_b_1714_;
v_isShared_1725_ = v_isSharedCheck_1777_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snd_1722_);
lean_dec(v_b_1714_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1777_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_array_1726_; lean_object* v_start_1727_; lean_object* v_stop_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_array_1726_ = lean_ctor_get(v_snd_1722_, 0);
v_start_1727_ = lean_ctor_get(v_snd_1722_, 1);
v_stop_1728_ = lean_ctor_get(v_snd_1722_, 2);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_nat_dec_lt(v_start_1727_, v_stop_1728_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1732_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1729_);
v___x_1732_ = v___x_1724_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_snd_1722_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
else
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1773_; 
lean_inc(v_stop_1728_);
lean_inc(v_start_1727_);
lean_inc_ref(v_array_1726_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_snd_1722_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1774_ = lean_ctor_get(v_snd_1722_, 2);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_snd_1722_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_snd_1722_, 0);
lean_dec(v_unused_1776_);
v___x_1736_ = v_snd_1722_;
v_isShared_1737_ = v_isSharedCheck_1773_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_snd_1722_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1773_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_a_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v_a_1738_ = lean_array_uget_borrowed(v_as_1711_, v_i_1713_);
v___x_1739_ = lean_array_fget(v_array_1726_, v_start_1727_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_start_1727_, v___x_1740_);
lean_dec(v_start_1727_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1741_);
v___x_1743_ = v___x_1736_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_array_1726_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_stop_1728_);
v___x_1743_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; 
lean_inc(v_a_1738_);
v___x_1744_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1738_, v___x_1739_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1763_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1763_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1763_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_unbox(v_a_1745_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_a_1745_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1743_);
lean_ctor_set(v___x_1724_, 0, v___x_1750_);
v___x_1752_ = v___x_1724_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1743_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1752_);
v___x_1754_ = v___x_1747_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
else
{
lean_object* v___x_1758_; 
lean_del_object(v___x_1747_);
lean_dec(v_a_1745_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1743_);
lean_ctor_set(v___x_1724_, 0, v___x_1729_);
v___x_1758_ = v___x_1724_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1743_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
size_t v___x_1759_; size_t v___x_1760_; 
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_add(v_i_1713_, v___x_1759_);
v_i_1713_ = v___x_1760_;
v_b_1714_ = v___x_1758_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___x_1743_);
lean_del_object(v___x_1724_);
v_a_1764_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1744_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1744_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1779_, lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_b_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
size_t v_sz_boxed_1788_; size_t v_i_boxed_1789_; lean_object* v_res_1790_; 
v_sz_boxed_1788_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1789_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1779_, v_sz_boxed_1788_, v_i_boxed_1789_, v_b_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v_as_1779_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1791_, lean_object* v_params2_1792_, lean_object* v___x_1793_, lean_object* v_params1_1794_, uint8_t v___x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
if (v___x_1791_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v___x_1793_);
lean_dec_ref(v_params2_1792_);
v___x_1801_ = lean_box(v___x_1791_);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; size_t v_sz_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = l_Array_toSubarray___redArg(v_params2_1792_, v___x_1803_, v___x_1793_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1804_);
v_sz_1807_ = lean_array_size(v_params1_1794_);
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1794_, v_sz_1807_, v___x_1808_, v___x_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1823_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1823_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_fst_1814_; 
v_fst_1814_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_fst_1814_);
lean_dec(v_a_1810_);
if (lean_obj_tag(v_fst_1814_) == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_box(v___x_1795_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1815_);
v___x_1817_ = v___x_1812_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1821_; 
v_val_1819_ = lean_ctor_get(v_fst_1814_, 0);
lean_inc(v_val_1819_);
lean_dec_ref_known(v_fst_1814_, 1);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v_val_1819_);
v___x_1821_ = v___x_1812_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1809_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1809_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1832_, lean_object* v_params2_1833_, lean_object* v___x_1834_, lean_object* v_params1_1835_, lean_object* v___x_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
uint8_t v___x_2007__boxed_1842_; uint8_t v___x_2009__boxed_1843_; lean_object* v_res_1844_; 
v___x_2007__boxed_1842_ = lean_unbox(v___x_1832_);
v___x_2009__boxed_1843_ = lean_unbox(v___x_1836_);
v_res_1844_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1842_, v_params2_1833_, v___x_1834_, v_params1_1835_, v___x_2009__boxed_1843_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec_ref(v_params1_1835_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1845_, lean_object* v_params2_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___y_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; 
v___x_1852_ = lean_array_get_size(v_params1_1845_);
v___x_1853_ = lean_array_get_size(v_params2_1846_);
v___x_1854_ = lean_nat_dec_eq(v___x_1852_, v___x_1853_);
v___x_1855_ = 1;
v___x_1856_ = lean_box(v___x_1854_);
v___x_1857_ = lean_box(v___x_1855_);
v___y_1858_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1858_, 0, v___x_1856_);
lean_closure_set(v___y_1858_, 1, v_params2_1846_);
lean_closure_set(v___y_1858_, 2, v___x_1853_);
lean_closure_set(v___y_1858_, 3, v_params1_1845_);
lean_closure_set(v___y_1858_, 4, v___x_1857_);
v___x_1859_ = 0;
v___x_1860_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1858_, v___x_1859_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1861_, lean_object* v_params2_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1861_, v_params2_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; lean_object* v_env_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_st_ref_get(v___y_1870_);
v_env_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_env_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1873_, v_declName_1869_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1876_, v___y_1877_);
lean_dec(v___y_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1880_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1894_; lean_object* v_dummy_1895_; 
v___x_1894_ = lean_box(0);
v_dummy_1895_ = l_Lean_Expr_sort___override(v___x_1894_);
return v_dummy_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1896_, lean_object* v_induct_1897_, lean_object* v_params_1898_, lean_object* v_idx_1899_, lean_object* v_e_1900_, lean_object* v_x_x3f_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
if (lean_obj_tag(v_e_1900_) == 11)
{
lean_object* v_typeName_1913_; lean_object* v_idx_1914_; lean_object* v_struct_1915_; uint8_t v___x_1962_; 
v_typeName_1913_ = lean_ctor_get(v_e_1900_, 0);
v_idx_1914_ = lean_ctor_get(v_e_1900_, 1);
v_struct_1915_ = lean_ctor_get(v_e_1900_, 2);
lean_inc_ref(v_struct_1915_);
v___x_1962_ = lean_nat_dec_eq(v_idx_1914_, v_idx_1899_);
if (v___x_1962_ == 0)
{
lean_dec_ref(v_struct_1915_);
lean_dec_ref_known(v_e_1900_, 3);
lean_dec_ref(v_params_1898_);
goto v___jp_1910_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_name_eq(v_induct_1897_, v_typeName_1913_);
if (v___x_1963_ == 0)
{
lean_dec_ref(v_struct_1915_);
lean_dec_ref_known(v_e_1900_, 3);
lean_dec_ref(v_params_1898_);
goto v___jp_1910_;
}
else
{
if (lean_obj_tag(v_x_x3f_1901_) == 0)
{
goto v___jp_1916_;
}
else
{
lean_object* v_val_1964_; uint8_t v___x_1965_; 
v_val_1964_ = lean_ctor_get(v_x_x3f_1901_, 0);
v___x_1965_ = lean_expr_eqv(v_val_1964_, v_struct_1915_);
if (v___x_1965_ == 0)
{
lean_dec_ref(v_struct_1915_);
lean_dec_ref_known(v_e_1900_, 3);
lean_dec_ref(v_params_1898_);
goto v___jp_1910_;
}
else
{
goto v___jp_1916_;
}
}
}
}
v___jp_1916_:
{
lean_object* v___x_1917_; 
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
v___x_1917_ = lean_infer_type(v_e_1900_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
v___x_1919_ = lean_whnf(v_a_1918_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_dummy_1921_; lean_object* v_nargs_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_dummy_1921_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1922_ = l_Lean_Expr_getAppNumArgs(v_a_1920_);
lean_inc(v_nargs_1922_);
v___x_1923_ = lean_mk_array(v_nargs_1922_, v_dummy_1921_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_sub(v_nargs_1922_, v___x_1924_);
lean_dec(v_nargs_1922_);
v___x_1926_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1920_, v___x_1923_, v___x_1925_);
v___x_1927_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1898_, v___x_1926_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1937_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
if (v___x_1932_ == 0)
{
lean_del_object(v___x_1930_);
lean_dec_ref(v_struct_1915_);
goto v___jp_1910_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_struct_1915_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_struct_1915_);
v_a_1938_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1927_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1927_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_struct_1915_);
lean_dec_ref(v_params_1898_);
v_a_1946_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1919_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1919_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_struct_1915_);
lean_dec_ref(v_params_1898_);
v_a_1954_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1917_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1917_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
else
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Expr_getAppFn(v_e_1900_);
if (lean_obj_tag(v___x_1966_) == 4)
{
lean_object* v_declName_1967_; lean_object* v___x_1968_; lean_object* v_a_1969_; 
v_declName_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_declName_1967_);
lean_dec_ref_known(v___x_1966_, 2);
v___x_1968_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1967_, v_a_1905_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
if (lean_obj_tag(v_a_1969_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2014_; 
v_val_1970_ = lean_ctor_get(v_a_1969_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1969_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1972_ = v_a_1969_;
v_isShared_1973_ = v_isSharedCheck_2014_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v_a_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2014_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_ctorName_1974_; lean_object* v_numParams_1975_; lean_object* v_i_1976_; uint8_t v___x_1977_; 
v_ctorName_1974_ = lean_ctor_get(v_val_1970_, 0);
lean_inc(v_ctorName_1974_);
v_numParams_1975_ = lean_ctor_get(v_val_1970_, 1);
lean_inc(v_numParams_1975_);
v_i_1976_ = lean_ctor_get(v_val_1970_, 2);
lean_inc(v_i_1976_);
lean_dec(v_val_1970_);
v___x_1977_ = lean_name_eq(v_ctorName_1974_, v_ctor_1896_);
lean_dec(v_ctorName_1974_);
if (v___x_1977_ == 0)
{
lean_dec(v_i_1976_);
lean_dec(v_numParams_1975_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_eq(v_i_1976_, v_idx_1899_);
lean_dec(v_i_1976_);
if (v___x_1978_ == 0)
{
lean_dec(v_numParams_1975_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1979_ = l_Lean_Expr_getAppNumArgs(v_e_1900_);
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_add(v_numParams_1975_, v___x_1980_);
lean_dec(v_numParams_1975_);
v___x_1982_ = lean_nat_dec_eq(v___x_1979_, v___x_1981_);
lean_dec(v___x_1981_);
lean_dec(v___x_1979_);
if (v___x_1982_ == 0)
{
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Expr_appArg_x21(v_e_1900_);
if (lean_obj_tag(v_x_x3f_1901_) == 0)
{
goto v___jp_1984_;
}
else
{
lean_object* v_val_2012_; uint8_t v___x_2013_; 
v_val_2012_ = lean_ctor_get(v_x_x3f_1901_, 0);
v___x_2013_ = lean_expr_eqv(v_val_2012_, v___x_1983_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v___x_1983_);
lean_del_object(v___x_1972_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
else
{
goto v___jp_1984_;
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v_dummy_1986_; lean_object* v_nargs_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1985_ = l_Lean_Expr_appFn_x21(v_e_1900_);
lean_dec_ref(v_e_1900_);
v_dummy_1986_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1987_ = l_Lean_Expr_getAppNumArgs(v___x_1985_);
lean_inc(v_nargs_1987_);
v___x_1988_ = lean_mk_array(v_nargs_1987_, v_dummy_1986_);
v___x_1989_ = lean_nat_sub(v_nargs_1987_, v___x_1980_);
lean_dec(v_nargs_1987_);
v___x_1990_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1985_, v___x_1988_, v___x_1989_);
v___x_1991_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1898_, v___x_1990_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
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
lean_dec_ref(v___x_1983_);
lean_del_object(v___x_1972_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1998_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1983_);
v___x_1998_ = v___x_1972_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1983_);
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
lean_dec_ref(v___x_1983_);
lean_del_object(v___x_1972_);
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
}
}
}
else
{
lean_dec(v_a_1969_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
}
else
{
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_params_1898_);
goto v___jp_1907_;
}
}
v___jp_1907_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
v___jp_1910_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2015_, lean_object* v_induct_2016_, lean_object* v_params_2017_, lean_object* v_idx_2018_, lean_object* v_e_2019_, lean_object* v_x_x3f_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2015_, v_induct_2016_, v_params_2017_, v_idx_2018_, v_e_2019_, v_x_x3f_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_x_x3f_2020_);
lean_dec(v_idx_2018_);
lean_dec(v_induct_2016_);
lean_dec(v_ctor_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v_env_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2033_ = lean_st_ref_get(v___y_2031_);
v_env_2037_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_ref(v_env_2037_);
lean_dec(v___x_2033_);
v___x_2038_ = 0;
v___x_2039_ = l_Lean_Environment_findAsync_x3f(v_env_2037_, v_constName_2027_, v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 1)
{
lean_object* v_val_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2059_; 
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2059_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_val_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2059_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v_kind_2044_; 
v_kind_2044_ = lean_ctor_get_uint8(v_val_2040_, sizeof(void*)*3);
if (v_kind_2044_ == 6)
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2040_);
if (lean_obj_tag(v___x_2045_) == 6)
{
lean_object* v_val_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_val_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_val_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v_val_2046_);
v___x_2051_ = v___x_2042_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_val_2046_);
v___x_2051_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2053_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2051_);
v___x_2053_ = v___x_2048_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v___x_2045_);
lean_del_object(v___x_2042_);
v___x_2057_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2058_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2057_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2058_;
}
}
else
{
lean_del_object(v___x_2042_);
lean_dec(v_val_2040_);
goto v___jp_2034_;
}
}
}
else
{
lean_dec(v___x_2039_);
goto v___jp_2034_;
}
v___jp_2034_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v_declName_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v_a_2081_, lean_object* v_val_2082_, lean_object* v_a_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_nat_dec_lt(v_a_2083_, v_upperBound_2075_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_a_2083_);
lean_dec_ref(v___x_2080_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_b_2084_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v_b_2084_);
v___x_2092_ = l_Lean_instInhabitedExpr;
v___x_2093_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2094_ = lean_nat_add(v___x_2076_, v_a_2083_);
v___x_2095_ = lean_array_get_borrowed(v___x_2092_, v___x_2077_, v___x_2094_);
lean_dec(v___x_2094_);
lean_inc(v___x_2095_);
lean_inc_ref(v___x_2080_);
v___x_2096_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2078_, v___x_2079_, v___x_2080_, v_a_2083_, v___x_2095_, v_a_2081_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2114_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2114_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2114_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
if (lean_obj_tag(v_a_2097_) == 1)
{
lean_object* v_val_2101_; uint8_t v___x_2102_; 
v_val_2101_ = lean_ctor_get(v_a_2097_, 0);
lean_inc(v_val_2101_);
lean_dec_ref_known(v_a_2097_, 1);
v___x_2102_ = lean_expr_eqv(v_val_2101_, v_val_2082_);
lean_dec(v_val_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec(v_a_2083_);
lean_dec_ref(v___x_2080_);
v___x_2103_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_del_object(v___x_2099_);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = lean_nat_add(v_a_2083_, v___x_2107_);
lean_dec(v_a_2083_);
v_a_2083_ = v___x_2108_;
v_b_2084_ = v___x_2093_;
goto _start;
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
lean_dec(v_a_2097_);
lean_dec(v_a_2083_);
lean_dec_ref(v___x_2080_);
v___x_2110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2110_);
v___x_2112_ = v___x_2099_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
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
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec(v_a_2083_);
lean_dec_ref(v___x_2080_);
v_a_2115_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2096_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2096_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_declName_2126_, lean_object* v___x_2127_, lean_object* v___x_2128_, lean_object* v_a_2129_, lean_object* v_val_2130_, lean_object* v_a_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2123_, v___x_2124_, v___x_2125_, v_declName_2126_, v___x_2127_, v___x_2128_, v_a_2129_, v_val_2130_, v_a_2131_, v_b_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_val_2130_);
lean_dec(v_a_2129_);
lean_dec(v___x_2127_);
lean_dec(v_declName_2126_);
lean_dec_ref(v___x_2125_);
lean_dec(v___x_2124_);
lean_dec(v_upperBound_2123_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2139_, lean_object* v_p_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Expr_getAppFn(v_e_2139_);
if (lean_obj_tag(v___x_2146_) == 4)
{
lean_object* v_declName_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_declName_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_n(v_declName_2147_, 2);
lean_dec_ref_known(v___x_2146_, 2);
v___x_2148_ = l_Lean_instInhabitedExpr;
v___x_2149_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2147_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2221_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2221_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2221_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_val_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2218_; 
v_val_2159_ = lean_ctor_get(v_a_2150_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2150_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2161_ = v_a_2150_;
v_isShared_2162_ = v_isSharedCheck_2218_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_val_2159_);
lean_dec(v_a_2150_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2218_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_induct_2163_; lean_object* v_numParams_2164_; lean_object* v_numFields_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_induct_2163_ = lean_ctor_get(v_val_2159_, 1);
lean_inc_n(v_induct_2163_, 2);
v_numParams_2164_ = lean_ctor_get(v_val_2159_, 3);
lean_inc(v_numParams_2164_);
v_numFields_2165_ = lean_ctor_get(v_val_2159_, 4);
lean_inc(v_numFields_2165_);
lean_dec(v_val_2159_);
v___x_2166_ = lean_apply_1(v_p_2140_, v_induct_2163_);
v___x_2167_ = lean_unbox(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_del_object(v___x_2152_);
lean_dec(v_declName_2147_);
lean_dec_ref(v_e_2139_);
v___x_2168_ = lean_box(0);
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2168_);
v___x_2170_ = v___x_2161_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
lean_del_object(v___x_2161_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = lean_nat_dec_lt(v___x_2172_, v_numFields_2165_);
if (v___x_2173_ == 0)
{
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2147_);
lean_dec_ref(v_e_2139_);
goto v___jp_2154_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = l_Lean_Expr_getAppNumArgs(v_e_2139_);
v___x_2175_ = lean_nat_add(v_numParams_2164_, v_numFields_2165_);
v___x_2176_ = lean_nat_dec_eq(v___x_2174_, v___x_2175_);
lean_dec(v___x_2175_);
if (v___x_2176_ == 0)
{
lean_dec(v___x_2174_);
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2147_);
lean_dec_ref(v_e_2139_);
goto v___jp_2154_;
}
else
{
lean_object* v_dummy_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_del_object(v___x_2152_);
v_dummy_2177_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2174_);
v___x_2178_ = lean_mk_array(v___x_2174_, v_dummy_2177_);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_sub(v___x_2174_, v___x_2179_);
lean_dec(v___x_2174_);
v___x_2181_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2139_, v___x_2178_, v___x_2180_);
lean_inc(v_numParams_2164_);
v___x_2182_ = l_Array_extract___redArg(v___x_2181_, v___x_2172_, v_numParams_2164_);
v___x_2183_ = lean_array_get_borrowed(v___x_2148_, v___x_2181_, v_numParams_2164_);
v___x_2184_ = lean_box(0);
lean_inc(v___x_2183_);
lean_inc_ref(v___x_2182_);
v___x_2185_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2147_, v_induct_2163_, v___x_2182_, v___x_2172_, v___x_2183_, v___x_2184_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2217_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2217_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2217_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
if (lean_obj_tag(v_a_2186_) == 1)
{
lean_object* v_val_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_del_object(v___x_2188_);
v_val_2190_ = lean_ctor_get(v_a_2186_, 0);
v___x_2191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2165_, v_numParams_2164_, v___x_2181_, v_declName_2147_, v_induct_2163_, v___x_2182_, v_a_2186_, v_val_2190_, v___x_2179_, v___x_2191_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2147_);
lean_dec_ref(v___x_2181_);
lean_dec(v_numParams_2164_);
lean_dec(v_numFields_2165_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2205_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2205_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_fst_2197_; 
v_fst_2197_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_fst_2197_);
lean_dec(v_a_2193_);
if (lean_obj_tag(v_fst_2197_) == 0)
{
lean_object* v___x_2199_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v_a_2186_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2186_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
else
{
lean_object* v_val_2201_; lean_object* v___x_2203_; 
lean_dec_ref_known(v_a_2186_, 1);
v_val_2201_ = lean_ctor_get(v_fst_2197_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v_fst_2197_, 1);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v_val_2201_);
v___x_2203_ = v___x_2195_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_val_2201_);
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
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref_known(v_a_2186_, 1);
v_a_2206_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2192_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2192_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
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
lean_object* v___x_2215_; 
lean_dec(v_a_2186_);
lean_dec_ref(v___x_2182_);
lean_dec_ref(v___x_2181_);
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2147_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2184_);
v___x_2215_ = v___x_2188_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2184_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_dec_ref(v___x_2182_);
lean_dec_ref(v___x_2181_);
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2147_);
return v___x_2185_;
}
}
}
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_del_object(v___x_2152_);
lean_dec(v_a_2150_);
lean_dec(v_declName_2147_);
lean_dec_ref(v_p_2140_);
lean_dec_ref(v_e_2139_);
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
v___jp_2154_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_box(0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2155_);
v___x_2157_ = v___x_2152_;
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
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_declName_2147_);
lean_dec_ref(v_p_2140_);
lean_dec_ref(v_e_2139_);
v_a_2222_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2149_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2149_);
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
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v___x_2146_);
lean_dec_ref(v_p_2140_);
lean_dec_ref(v_e_2139_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2232_, lean_object* v_p_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_etaStruct_x3f(v_e_2232_, v_p_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2240_, lean_object* v___x_2241_, lean_object* v___x_2242_, lean_object* v_declName_2243_, lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v_a_2246_, lean_object* v_val_2247_, lean_object* v_inst_2248_, lean_object* v_R_2249_, lean_object* v_a_2250_, lean_object* v_b_2251_, lean_object* v_c_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2240_, v___x_2241_, v___x_2242_, v_declName_2243_, v___x_2244_, v___x_2245_, v_a_2246_, v_val_2247_, v_a_2250_, v_b_2251_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2259_ = _args[0];
lean_object* v___x_2260_ = _args[1];
lean_object* v___x_2261_ = _args[2];
lean_object* v_declName_2262_ = _args[3];
lean_object* v___x_2263_ = _args[4];
lean_object* v___x_2264_ = _args[5];
lean_object* v_a_2265_ = _args[6];
lean_object* v_val_2266_ = _args[7];
lean_object* v_inst_2267_ = _args[8];
lean_object* v_R_2268_ = _args[9];
lean_object* v_a_2269_ = _args[10];
lean_object* v_b_2270_ = _args[11];
lean_object* v_c_2271_ = _args[12];
lean_object* v___y_2272_ = _args[13];
lean_object* v___y_2273_ = _args[14];
lean_object* v___y_2274_ = _args[15];
lean_object* v___y_2275_ = _args[16];
lean_object* v___y_2276_ = _args[17];
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2259_, v___x_2260_, v___x_2261_, v_declName_2262_, v___x_2263_, v___x_2264_, v_a_2265_, v_val_2266_, v_inst_2267_, v_R_2268_, v_a_2269_, v_b_2270_, v_c_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_val_2266_);
lean_dec(v_a_2265_);
lean_dec(v___x_2263_);
lean_dec(v_declName_2262_);
lean_dec_ref(v___x_2261_);
lean_dec(v___x_2260_);
lean_dec(v_upperBound_2259_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = l_Lean_Expr_hasMVar(v_e_2278_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_e_2278_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v_mctx_2284_; lean_object* v___x_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v___x_2288_; lean_object* v_cache_2289_; lean_object* v_zetaDeltaFVarIds_2290_; lean_object* v_postponed_2291_; lean_object* v_diag_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2301_; 
v___x_2283_ = lean_st_ref_get(v___y_2279_);
v_mctx_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc_ref(v_mctx_2284_);
lean_dec(v___x_2283_);
v___x_2285_ = l_Lean_instantiateMVarsCore(v_mctx_2284_, v_e_2278_);
v_fst_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v___x_2285_, 1);
lean_inc(v_snd_2287_);
lean_dec_ref(v___x_2285_);
v___x_2288_ = lean_st_ref_take(v___y_2279_);
v_cache_2289_ = lean_ctor_get(v___x_2288_, 1);
v_zetaDeltaFVarIds_2290_ = lean_ctor_get(v___x_2288_, 2);
v_postponed_2291_ = lean_ctor_get(v___x_2288_, 3);
v_diag_2292_ = lean_ctor_get(v___x_2288_, 4);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2288_, 0);
lean_dec(v_unused_2302_);
v___x_2294_ = v___x_2288_;
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_diag_2292_);
lean_inc(v_postponed_2291_);
lean_inc(v_zetaDeltaFVarIds_2290_);
lean_inc(v_cache_2289_);
lean_dec(v___x_2288_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_snd_2287_);
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_snd_2287_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_cache_2289_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_zetaDeltaFVarIds_2290_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_postponed_2291_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_diag_2292_);
v___x_2297_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_st_ref_put(v___y_2279_, v___x_2297_);
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_fst_2286_);
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2303_, v___y_2304_);
lean_dec(v___y_2304_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2307_, v___y_2309_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_x_2331_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2338_, lean_object* v_e_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_etaStruct_x3f(v_e_2339_, v_p_2338_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2365_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2365_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2365_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
if (lean_obj_tag(v_a_2346_) == 1)
{
lean_object* v_val_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2360_; 
v_val_2350_ = lean_ctor_get(v_a_2346_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2352_ = v_a_2346_;
v_isShared_2353_ = v_isSharedCheck_2360_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_val_2350_);
lean_dec(v_a_2346_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2360_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 0);
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_val_2350_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2355_);
v___x_2357_ = v___x_2348_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
lean_dec(v_a_2346_);
v___x_2361_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2361_);
v___x_2363_ = v___x_2348_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
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
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_a_2366_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2345_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2345_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2374_, lean_object* v_e_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2374_, v_e_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1(lean_object* v_x_2382_, lean_object* v_e_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_e_2383_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1___boxed(lean_object* v_x_2390_, lean_object* v_e_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__1(v_x_2390_, v_e_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_x_2390_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_apply_1(v_x_2399_, lean_box(0));
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2407_, v_x_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2415_, lean_object* v_b_2416_, lean_object* v_x_2417_){
_start:
{
if (lean_obj_tag(v_x_2417_) == 0)
{
lean_dec(v_b_2416_);
lean_dec_ref(v_a_2415_);
return v_x_2417_;
}
else
{
lean_object* v_key_2418_; lean_object* v_value_2419_; lean_object* v_tail_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2432_; 
v_key_2418_ = lean_ctor_get(v_x_2417_, 0);
v_value_2419_ = lean_ctor_get(v_x_2417_, 1);
v_tail_2420_ = lean_ctor_get(v_x_2417_, 2);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2417_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2422_ = v_x_2417_;
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_tail_2420_);
lean_inc(v_value_2419_);
lean_inc(v_key_2418_);
lean_dec(v_x_2417_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
uint8_t v___x_2424_; 
v___x_2424_ = l_Lean_ExprStructEq_beq(v_key_2418_, v_a_2415_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2415_, v_b_2416_, v_tail_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 2, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_key_2418_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_value_2419_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v___x_2430_; 
lean_dec(v_value_2419_);
lean_dec(v_key_2418_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v_b_2416_);
lean_ctor_set(v___x_2422_, 0, v_a_2415_);
v___x_2430_ = v___x_2422_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_b_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_tail_2420_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
return v_x_2433_;
}
else
{
lean_object* v_key_2435_; lean_object* v_value_2436_; lean_object* v_tail_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2460_; 
v_key_2435_ = lean_ctor_get(v_x_2434_, 0);
v_value_2436_ = lean_ctor_get(v_x_2434_, 1);
v_tail_2437_ = lean_ctor_get(v_x_2434_, 2);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_x_2434_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2439_ = v_x_2434_;
v_isShared_2440_ = v_isSharedCheck_2460_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_tail_2437_);
lean_inc(v_value_2436_);
lean_inc(v_key_2435_);
lean_dec(v_x_2434_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2460_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; uint64_t v_fold_2445_; uint64_t v___x_2446_; uint64_t v___x_2447_; uint64_t v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2441_ = lean_array_get_size(v_x_2433_);
v___x_2442_ = l_Lean_ExprStructEq_hash(v_key_2435_);
v___x_2443_ = 32ULL;
v___x_2444_ = lean_uint64_shift_right(v___x_2442_, v___x_2443_);
v_fold_2445_ = lean_uint64_xor(v___x_2442_, v___x_2444_);
v___x_2446_ = 16ULL;
v___x_2447_ = lean_uint64_shift_right(v_fold_2445_, v___x_2446_);
v___x_2448_ = lean_uint64_xor(v_fold_2445_, v___x_2447_);
v___x_2449_ = lean_uint64_to_usize(v___x_2448_);
v___x_2450_ = lean_usize_of_nat(v___x_2441_);
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_sub(v___x_2450_, v___x_2451_);
v___x_2453_ = lean_usize_land(v___x_2449_, v___x_2452_);
v___x_2454_ = lean_array_uget_borrowed(v_x_2433_, v___x_2453_);
lean_inc(v___x_2454_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 2, v___x_2454_);
v___x_2456_ = v___x_2439_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_key_2435_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_value_2436_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_array_uset(v_x_2433_, v___x_2453_, v___x_2456_);
v_x_2433_ = v___x_2457_;
v_x_2434_ = v_tail_2437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2461_, lean_object* v_source_2462_, lean_object* v_target_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_array_get_size(v_source_2462_);
v___x_2465_ = lean_nat_dec_lt(v_i_2461_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_dec_ref(v_source_2462_);
lean_dec(v_i_2461_);
return v_target_2463_;
}
else
{
lean_object* v_es_2466_; lean_object* v___x_2467_; lean_object* v_source_2468_; lean_object* v_target_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_es_2466_ = lean_array_fget(v_source_2462_, v_i_2461_);
v___x_2467_ = lean_box(0);
v_source_2468_ = lean_array_fset(v_source_2462_, v_i_2461_, v___x_2467_);
v_target_2469_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2463_, v_es_2466_);
v___x_2470_ = lean_unsigned_to_nat(1u);
v___x_2471_ = lean_nat_add(v_i_2461_, v___x_2470_);
lean_dec(v_i_2461_);
v_i_2461_ = v___x_2471_;
v_source_2462_ = v_source_2468_;
v_target_2463_ = v_target_2469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_nbuckets_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2474_ = lean_array_get_size(v_data_2473_);
v___x_2475_ = lean_unsigned_to_nat(2u);
v_nbuckets_2476_ = lean_nat_mul(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_mk_array(v_nbuckets_2476_, v___x_2478_);
v___x_2480_ = lean_array_propagate_mark(v_data_2473_, v___x_2479_);
v___x_2481_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2477_, v_data_2473_, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2482_, lean_object* v_x_2483_){
_start:
{
if (lean_obj_tag(v_x_2483_) == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = 0;
return v___x_2484_;
}
else
{
lean_object* v_key_2485_; lean_object* v_tail_2486_; uint8_t v___x_2487_; 
v_key_2485_ = lean_ctor_get(v_x_2483_, 0);
v_tail_2486_ = lean_ctor_get(v_x_2483_, 2);
v___x_2487_ = l_Lean_ExprStructEq_beq(v_key_2485_, v_a_2482_);
if (v___x_2487_ == 0)
{
v_x_2483_ = v_tail_2486_;
goto _start;
}
else
{
return v___x_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2489_, lean_object* v_x_2490_){
_start:
{
uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_res_2491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2489_, v_x_2490_);
lean_dec(v_x_2490_);
lean_dec_ref(v_a_2489_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2493_, lean_object* v_a_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v_size_2496_; lean_object* v_buckets_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2540_; 
v_size_2496_ = lean_ctor_get(v_m_2493_, 0);
v_buckets_2497_ = lean_ctor_get(v_m_2493_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_m_2493_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2499_ = v_m_2493_;
v_isShared_2500_ = v_isSharedCheck_2540_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_buckets_2497_);
lean_inc(v_size_2496_);
lean_dec(v_m_2493_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2540_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; uint64_t v___x_2502_; uint64_t v___x_2503_; uint64_t v___x_2504_; uint64_t v_fold_2505_; uint64_t v___x_2506_; uint64_t v___x_2507_; uint64_t v___x_2508_; size_t v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; size_t v___x_2513_; lean_object* v_bkt_2514_; uint8_t v___x_2515_; 
v___x_2501_ = lean_array_get_size(v_buckets_2497_);
v___x_2502_ = l_Lean_ExprStructEq_hash(v_a_2494_);
v___x_2503_ = 32ULL;
v___x_2504_ = lean_uint64_shift_right(v___x_2502_, v___x_2503_);
v_fold_2505_ = lean_uint64_xor(v___x_2502_, v___x_2504_);
v___x_2506_ = 16ULL;
v___x_2507_ = lean_uint64_shift_right(v_fold_2505_, v___x_2506_);
v___x_2508_ = lean_uint64_xor(v_fold_2505_, v___x_2507_);
v___x_2509_ = lean_uint64_to_usize(v___x_2508_);
v___x_2510_ = lean_usize_of_nat(v___x_2501_);
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_sub(v___x_2510_, v___x_2511_);
v___x_2513_ = lean_usize_land(v___x_2509_, v___x_2512_);
v_bkt_2514_ = lean_array_uget_borrowed(v_buckets_2497_, v___x_2513_);
v___x_2515_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2494_, v_bkt_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v_size_x27_2517_; lean_object* v___x_2518_; lean_object* v_buckets_x27_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2516_ = lean_unsigned_to_nat(1u);
v_size_x27_2517_ = lean_nat_add(v_size_2496_, v___x_2516_);
lean_dec(v_size_2496_);
lean_inc(v_bkt_2514_);
v___x_2518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2518_, 0, v_a_2494_);
lean_ctor_set(v___x_2518_, 1, v_b_2495_);
lean_ctor_set(v___x_2518_, 2, v_bkt_2514_);
v_buckets_x27_2519_ = lean_array_uset(v_buckets_2497_, v___x_2513_, v___x_2518_);
v___x_2520_ = lean_unsigned_to_nat(4u);
v___x_2521_ = lean_nat_mul(v_size_x27_2517_, v___x_2520_);
v___x_2522_ = lean_unsigned_to_nat(3u);
v___x_2523_ = lean_nat_div(v___x_2521_, v___x_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_array_get_size(v_buckets_x27_2519_);
v___x_2525_ = lean_nat_dec_le(v___x_2523_, v___x_2524_);
lean_dec(v___x_2523_);
if (v___x_2525_ == 0)
{
lean_object* v_val_2526_; lean_object* v___x_2528_; 
v_val_2526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2519_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v_val_2526_);
lean_ctor_set(v___x_2499_, 0, v_size_x27_2517_);
v___x_2528_ = v___x_2499_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_size_x27_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_val_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
else
{
lean_object* v___x_2531_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v_buckets_x27_2519_);
lean_ctor_set(v___x_2499_, 0, v_size_x27_2517_);
v___x_2531_ = v___x_2499_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_size_x27_2517_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_buckets_x27_2519_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v___x_2533_; lean_object* v_buckets_x27_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_inc(v_bkt_2514_);
v___x_2533_ = lean_box(0);
v_buckets_x27_2534_ = lean_array_uset(v_buckets_2497_, v___x_2513_, v___x_2533_);
v___x_2535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2494_, v_b_2495_, v_bkt_2514_);
v___x_2536_ = lean_array_uset(v_buckets_x27_2534_, v___x_2513_, v___x_2535_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v___x_2536_);
v___x_2538_ = v___x_2499_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_size_2496_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2541_, lean_object* v_e_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2545_ = lean_st_ref_take(v_a_2541_);
v___x_2546_ = lean_box(0);
v___x_2547_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2545_, v_e_2542_, v_a_2543_);
v___x_2548_ = lean_st_ref_put(v_a_2541_, v___x_2547_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2549_, lean_object* v_e_2550_, lean_object* v_a_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2549_, v_e_2550_, v_a_2551_);
lean_dec(v_a_2549_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_apply_1(v_x_2555_, lean_box(0));
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2563_, v_x_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2571_, lean_object* v___y_2572_, lean_object* v_b_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
lean_inc(v___y_2572_);
v___x_2579_ = lean_apply_7(v_k_2571_, v_b_2573_, v___y_2572_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, lean_box(0));
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2580_, lean_object* v___y_2581_, lean_object* v_b_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2580_, v___y_2581_, v_b_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2581_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2589_, uint8_t v_bi_2590_, lean_object* v_type_2591_, lean_object* v_k_2592_, uint8_t v_kind_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___f_2600_; lean_object* v___x_2601_; 
lean_inc(v___y_2594_);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2600_, 0, v_k_2592_);
lean_closure_set(v___f_2600_, 1, v___y_2594_);
v___x_2601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2589_, v_bi_2590_, v_type_2591_, v___f_2600_, v_kind_2593_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2601_) == 0)
{
return v___x_2601_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2610_, lean_object* v_bi_2611_, lean_object* v_type_2612_, lean_object* v_k_2613_, lean_object* v_kind_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v_bi_boxed_2621_; uint8_t v_kind_boxed_2622_; lean_object* v_res_2623_; 
v_bi_boxed_2621_ = lean_unbox(v_bi_2611_);
v_kind_boxed_2622_ = lean_unbox(v_kind_2614_);
v_res_2623_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2610_, v_bi_boxed_2621_, v_type_2612_, v_k_2613_, v_kind_boxed_2622_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2(lean_object* v___x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2624_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2___boxed(lean_object* v___x_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2(v___x_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2638_, lean_object* v_type_2639_, lean_object* v_val_2640_, lean_object* v_k_2641_, uint8_t v_nondep_2642_, uint8_t v_kind_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; 
lean_inc(v___y_2644_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2650_, 0, v_k_2641_);
lean_closure_set(v___f_2650_, 1, v___y_2644_);
v___x_2651_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2638_, v_type_2639_, v_val_2640_, v___f_2650_, v_nondep_2642_, v_kind_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2651_) == 0)
{
return v___x_2651_;
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2660_, lean_object* v_type_2661_, lean_object* v_val_2662_, lean_object* v_k_2663_, lean_object* v_nondep_2664_, lean_object* v_kind_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_nondep_boxed_2672_; uint8_t v_kind_boxed_2673_; lean_object* v_res_2674_; 
v_nondep_boxed_2672_ = lean_unbox(v_nondep_2664_);
v_kind_boxed_2673_ = lean_unbox(v_kind_2665_);
v_res_2674_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2660_, v_type_2661_, v_val_2662_, v_k_2663_, v_nondep_boxed_2672_, v_kind_boxed_2673_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
return v_res_2674_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = l_Lean_maxRecDepthErrorMessage;
v___x_2681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2683_ = l_Lean_MessageData_ofFormat(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2685_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2686_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v___x_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_ref_2687_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___y_2703_; lean_object* v_toCold_2712_; lean_object* v_currRecDepth_2713_; lean_object* v_ref_2714_; uint16_t v_optionFlags_2715_; uint8_t v_suppressElabErrors_2716_; uint8_t v_isRecordingDeps_2717_; lean_object* v_maxRecDepth_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_toCold_2712_ = lean_ctor_get(v___y_2699_, 0);
v_currRecDepth_2713_ = lean_ctor_get(v___y_2699_, 1);
v_ref_2714_ = lean_ctor_get(v___y_2699_, 2);
v_optionFlags_2715_ = lean_ctor_get_uint16(v___y_2699_, sizeof(void*)*3);
v_suppressElabErrors_2716_ = lean_ctor_get_uint8(v___y_2699_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2717_ = lean_ctor_get_uint8(v___y_2699_, sizeof(void*)*3 + 3);
v_maxRecDepth_2723_ = lean_ctor_get(v_toCold_2712_, 3);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_nat_dec_eq(v_maxRecDepth_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_nat_dec_eq(v_currRecDepth_2713_, v_maxRecDepth_2723_);
if (v___x_2726_ == 0)
{
goto v___jp_2718_;
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_x_2695_);
lean_inc(v_ref_2714_);
v___x_2727_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2714_);
v___y_2703_ = v___x_2727_;
goto v___jp_2702_;
}
}
else
{
goto v___jp_2718_;
}
v___jp_2702_:
{
if (lean_obj_tag(v___y_2703_) == 0)
{
return v___y_2703_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_a_2704_ = lean_ctor_get(v___y_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___y_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___y_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___y_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
v___jp_2718_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2719_ = lean_unsigned_to_nat(1u);
v___x_2720_ = lean_nat_add(v_currRecDepth_2713_, v___x_2719_);
lean_inc(v_ref_2714_);
lean_inc_ref(v_toCold_2712_);
v___x_2721_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2721_, 0, v_toCold_2712_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
lean_ctor_set(v___x_2721_, 2, v_ref_2714_);
lean_ctor_set_uint16(v___x_2721_, sizeof(void*)*3, v_optionFlags_2715_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*3 + 2, v_suppressElabErrors_2716_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*3 + 3, v_isRecordingDeps_2717_);
lean_inc(v___y_2700_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
v___x_2722_ = lean_apply_6(v_x_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___x_2721_, v___y_2700_, lean_box(0));
v___y_2703_ = v___x_2722_;
goto v___jp_2702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_a_2736_, lean_object* v_x_2737_){
_start:
{
if (lean_obj_tag(v_x_2737_) == 0)
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_box(0);
return v___x_2738_;
}
else
{
lean_object* v_key_2739_; lean_object* v_value_2740_; lean_object* v_tail_2741_; uint8_t v___x_2742_; 
v_key_2739_ = lean_ctor_get(v_x_2737_, 0);
v_value_2740_ = lean_ctor_get(v_x_2737_, 1);
v_tail_2741_ = lean_ctor_get(v_x_2737_, 2);
v___x_2742_ = l_Lean_ExprStructEq_beq(v_key_2739_, v_a_2736_);
if (v___x_2742_ == 0)
{
v_x_2737_ = v_tail_2741_;
goto _start;
}
else
{
lean_object* v___x_2744_; 
lean_inc(v_value_2740_);
v___x_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_value_2740_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_a_2745_, lean_object* v_x_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2745_, v_x_2746_);
lean_dec(v_x_2746_);
lean_dec_ref(v_a_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(lean_object* v_m_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_buckets_2750_; lean_object* v___x_2751_; uint64_t v___x_2752_; uint64_t v___x_2753_; uint64_t v___x_2754_; uint64_t v_fold_2755_; uint64_t v___x_2756_; uint64_t v___x_2757_; uint64_t v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_buckets_2750_ = lean_ctor_get(v_m_2748_, 1);
v___x_2751_ = lean_array_get_size(v_buckets_2750_);
v___x_2752_ = l_Lean_ExprStructEq_hash(v_a_2749_);
v___x_2753_ = 32ULL;
v___x_2754_ = lean_uint64_shift_right(v___x_2752_, v___x_2753_);
v_fold_2755_ = lean_uint64_xor(v___x_2752_, v___x_2754_);
v___x_2756_ = 16ULL;
v___x_2757_ = lean_uint64_shift_right(v_fold_2755_, v___x_2756_);
v___x_2758_ = lean_uint64_xor(v_fold_2755_, v___x_2757_);
v___x_2759_ = lean_uint64_to_usize(v___x_2758_);
v___x_2760_ = lean_usize_of_nat(v___x_2751_);
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_sub(v___x_2760_, v___x_2761_);
v___x_2763_ = lean_usize_land(v___x_2759_, v___x_2762_);
v___x_2764_ = lean_array_uget_borrowed(v_buckets_2750_, v___x_2763_);
v___x_2765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_2749_, v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_m_2766_, v_a_2767_);
lean_dec_ref(v_a_2767_);
lean_dec_ref(v_m_2766_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2769_, lean_object* v_pre_2770_, lean_object* v_post_2771_, lean_object* v_usedLetOnly_2772_, lean_object* v_skipConstInApp_2773_, lean_object* v_skipInstances_2774_, lean_object* v_postApp_2775_, lean_object* v_body_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_usedLetOnly_boxed_2784_; uint8_t v_skipConstInApp_boxed_2785_; uint8_t v_skipInstances_boxed_2786_; lean_object* v_res_2787_; 
v_usedLetOnly_boxed_2784_ = lean_unbox(v_usedLetOnly_2772_);
v_skipConstInApp_boxed_2785_ = lean_unbox(v_skipConstInApp_2773_);
v_skipInstances_boxed_2786_ = lean_unbox(v_skipInstances_2774_);
v_res_2787_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2769_, v_pre_2770_, v_post_2771_, v_usedLetOnly_boxed_2784_, v_skipConstInApp_boxed_2785_, v_skipInstances_boxed_2786_, v_postApp_2775_, v_body_2776_, v_x_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2791_, lean_object* v_pre_2792_, lean_object* v_post_2793_, uint8_t v_usedLetOnly_2794_, uint8_t v_skipConstInApp_2795_, uint8_t v_skipInstances_2796_, lean_object* v_postApp_2797_, lean_object* v_body_2798_, lean_object* v_x_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_array_push(v_fvars_2791_, v_x_2799_);
v___x_2807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v_postApp_2797_, v___x_2806_, v_body_2798_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2808_, lean_object* v_pre_2809_, lean_object* v_post_2810_, lean_object* v_usedLetOnly_2811_, lean_object* v_skipConstInApp_2812_, lean_object* v_skipInstances_2813_, lean_object* v_postApp_2814_, lean_object* v_body_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_usedLetOnly_boxed_2823_; uint8_t v_skipConstInApp_boxed_2824_; uint8_t v_skipInstances_boxed_2825_; lean_object* v_res_2826_; 
v_usedLetOnly_boxed_2823_ = lean_unbox(v_usedLetOnly_2811_);
v_skipConstInApp_boxed_2824_ = lean_unbox(v_skipConstInApp_2812_);
v_skipInstances_boxed_2825_ = lean_unbox(v_skipInstances_2813_);
v_res_2826_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2808_, v_pre_2809_, v_post_2810_, v_usedLetOnly_boxed_2823_, v_skipConstInApp_boxed_2824_, v_skipInstances_boxed_2825_, v_postApp_2814_, v_body_2815_, v_x_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_pre_2827_, lean_object* v_post_2828_, uint8_t v_usedLetOnly_2829_, uint8_t v_skipConstInApp_2830_, uint8_t v_skipInstances_2831_, lean_object* v_postApp_2832_, lean_object* v_e_2833_, lean_object* v_a_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
lean_inc_ref(v_post_2828_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc_ref(v_e_2833_);
v___x_2840_ = lean_apply_6(v_post_2828_, v_e_2833_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, lean_box(0));
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2859_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2859_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2859_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
switch(lean_obj_tag(v_a_2841_))
{
case 0:
{
lean_object* v_e_2845_; lean_object* v___x_2847_; 
lean_dec_ref(v_e_2833_);
lean_dec_ref(v_postApp_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_e_2845_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_ref(v_e_2845_);
lean_dec_ref_known(v_a_2841_, 1);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_e_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_e_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
case 1:
{
lean_object* v_e_2849_; lean_object* v___x_2850_; 
lean_del_object(v___x_2843_);
lean_dec_ref(v_e_2833_);
v_e_2849_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_ref(v_e_2849_);
lean_dec_ref_known(v_a_2841_, 1);
v___x_2850_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2827_, v_post_2828_, v_usedLetOnly_2829_, v_skipConstInApp_2830_, v_skipInstances_2831_, v_postApp_2832_, v_e_2849_, v_a_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
return v___x_2850_;
}
default: 
{
lean_object* v_e_x3f_2851_; 
lean_dec_ref(v_postApp_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_e_x3f_2851_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_e_x3f_2851_);
lean_dec_ref_known(v_a_2841_, 1);
if (lean_obj_tag(v_e_x3f_2851_) == 0)
{
lean_object* v___x_2853_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_e_2833_);
v___x_2853_ = v___x_2843_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_e_2833_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
lean_object* v_val_2855_; lean_object* v___x_2857_; 
lean_dec_ref(v_e_2833_);
v_val_2855_ = lean_ctor_get(v_e_x3f_2851_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_e_x3f_2851_, 1);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_val_2855_);
v___x_2857_ = v___x_2843_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_val_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_e_2833_);
lean_dec_ref(v_postApp_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_a_2860_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2840_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2840_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2868_, lean_object* v_post_2869_, uint8_t v_usedLetOnly_2870_, uint8_t v_skipConstInApp_2871_, uint8_t v_skipInstances_2872_, lean_object* v_postApp_2873_, lean_object* v_fvars_2874_, lean_object* v_e_2875_, lean_object* v_a_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
if (lean_obj_tag(v_e_2875_) == 6)
{
lean_object* v_binderName_2882_; lean_object* v_binderType_2883_; lean_object* v_body_2884_; uint8_t v_binderInfo_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_binderName_2882_ = lean_ctor_get(v_e_2875_, 0);
lean_inc(v_binderName_2882_);
v_binderType_2883_ = lean_ctor_get(v_e_2875_, 1);
lean_inc_ref(v_binderType_2883_);
v_body_2884_ = lean_ctor_get(v_e_2875_, 2);
lean_inc_ref(v_body_2884_);
v_binderInfo_2885_ = lean_ctor_get_uint8(v_e_2875_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2875_, 3);
v___x_2886_ = lean_box(v_usedLetOnly_2870_);
v___x_2887_ = lean_box(v_skipConstInApp_2871_);
v___x_2888_ = lean_box(v_skipInstances_2872_);
lean_inc_ref(v_postApp_2873_);
lean_inc_ref(v_post_2869_);
lean_inc_ref(v_pre_2868_);
lean_inc_ref(v_fvars_2874_);
v___f_2889_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2889_, 0, v_fvars_2874_);
lean_closure_set(v___f_2889_, 1, v_pre_2868_);
lean_closure_set(v___f_2889_, 2, v_post_2869_);
lean_closure_set(v___f_2889_, 3, v___x_2886_);
lean_closure_set(v___f_2889_, 4, v___x_2887_);
lean_closure_set(v___f_2889_, 5, v___x_2888_);
lean_closure_set(v___f_2889_, 6, v_postApp_2873_);
lean_closure_set(v___f_2889_, 7, v_body_2884_);
v___x_2890_ = lean_expr_instantiate_rev(v_binderType_2883_, v_fvars_2874_);
lean_dec_ref(v_fvars_2874_);
lean_dec_ref(v_binderType_2883_);
v___x_2891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2868_, v_post_2869_, v_usedLetOnly_2870_, v_skipConstInApp_2871_, v_skipInstances_2872_, v_postApp_2873_, v___x_2890_, v_a_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = 0;
v___x_2894_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2882_, v_binderInfo_2885_, v_a_2892_, v___f_2889_, v___x_2893_, v_a_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2894_;
}
else
{
lean_dec_ref(v___f_2889_);
lean_dec(v_binderName_2882_);
return v___x_2891_;
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_expr_instantiate_rev(v_e_2875_, v_fvars_2874_);
lean_dec_ref(v_e_2875_);
lean_inc_ref(v_postApp_2873_);
lean_inc_ref(v_post_2869_);
lean_inc_ref(v_pre_2868_);
v___x_2896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2868_, v_post_2869_, v_usedLetOnly_2870_, v_skipConstInApp_2871_, v_skipInstances_2872_, v_postApp_2873_, v___x_2895_, v_a_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; uint8_t v___x_2898_; uint8_t v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = 0;
v___x_2899_ = 1;
v___x_2900_ = 1;
v___x_2901_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2874_, v_a_2897_, v___x_2898_, v_usedLetOnly_2870_, v___x_2898_, v___x_2899_, v___x_2900_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v_fvars_2874_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_2868_, v_post_2869_, v_usedLetOnly_2870_, v_skipConstInApp_2871_, v_skipInstances_2872_, v_postApp_2873_, v_a_2902_, v_a_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2903_;
}
else
{
lean_dec_ref(v_postApp_2873_);
lean_dec_ref(v_post_2869_);
lean_dec_ref(v_pre_2868_);
return v___x_2901_;
}
}
else
{
lean_dec_ref(v_fvars_2874_);
lean_dec_ref(v_postApp_2873_);
lean_dec_ref(v_post_2869_);
lean_dec_ref(v_pre_2868_);
return v___x_2896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2904_, lean_object* v_pre_2905_, lean_object* v_post_2906_, uint8_t v_usedLetOnly_2907_, uint8_t v_skipConstInApp_2908_, uint8_t v_skipInstances_2909_, lean_object* v_postApp_2910_, lean_object* v_body_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_array_push(v_fvars_2904_, v_x_2912_);
v___x_2920_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2905_, v_post_2906_, v_usedLetOnly_2907_, v_skipConstInApp_2908_, v_skipInstances_2909_, v_postApp_2910_, v___x_2919_, v_body_2911_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2921_, lean_object* v_pre_2922_, lean_object* v_post_2923_, lean_object* v_usedLetOnly_2924_, lean_object* v_skipConstInApp_2925_, lean_object* v_skipInstances_2926_, lean_object* v_postApp_2927_, lean_object* v_body_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_usedLetOnly_boxed_2936_; uint8_t v_skipConstInApp_boxed_2937_; uint8_t v_skipInstances_boxed_2938_; lean_object* v_res_2939_; 
v_usedLetOnly_boxed_2936_ = lean_unbox(v_usedLetOnly_2924_);
v_skipConstInApp_boxed_2937_ = lean_unbox(v_skipConstInApp_2925_);
v_skipInstances_boxed_2938_ = lean_unbox(v_skipInstances_2926_);
v_res_2939_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2921_, v_pre_2922_, v_post_2923_, v_usedLetOnly_boxed_2936_, v_skipConstInApp_boxed_2937_, v_skipInstances_boxed_2938_, v_postApp_2927_, v_body_2928_, v_x_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2940_, lean_object* v_post_2941_, uint8_t v_usedLetOnly_2942_, uint8_t v_skipConstInApp_2943_, uint8_t v_skipInstances_2944_, lean_object* v_postApp_2945_, lean_object* v_fvars_2946_, lean_object* v_e_2947_, lean_object* v_a_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
if (lean_obj_tag(v_e_2947_) == 8)
{
lean_object* v_declName_2954_; lean_object* v_type_2955_; lean_object* v_value_2956_; lean_object* v_body_2957_; uint8_t v_nondep_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_declName_2954_ = lean_ctor_get(v_e_2947_, 0);
lean_inc(v_declName_2954_);
v_type_2955_ = lean_ctor_get(v_e_2947_, 1);
lean_inc_ref(v_type_2955_);
v_value_2956_ = lean_ctor_get(v_e_2947_, 2);
lean_inc_ref(v_value_2956_);
v_body_2957_ = lean_ctor_get(v_e_2947_, 3);
lean_inc_ref(v_body_2957_);
v_nondep_2958_ = lean_ctor_get_uint8(v_e_2947_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2947_, 4);
v___x_2959_ = lean_box(v_usedLetOnly_2942_);
v___x_2960_ = lean_box(v_skipConstInApp_2943_);
v___x_2961_ = lean_box(v_skipInstances_2944_);
lean_inc_ref_n(v_postApp_2945_, 2);
lean_inc_ref_n(v_post_2941_, 2);
lean_inc_ref_n(v_pre_2940_, 2);
lean_inc_ref(v_fvars_2946_);
v___f_2962_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2962_, 0, v_fvars_2946_);
lean_closure_set(v___f_2962_, 1, v_pre_2940_);
lean_closure_set(v___f_2962_, 2, v_post_2941_);
lean_closure_set(v___f_2962_, 3, v___x_2959_);
lean_closure_set(v___f_2962_, 4, v___x_2960_);
lean_closure_set(v___f_2962_, 5, v___x_2961_);
lean_closure_set(v___f_2962_, 6, v_postApp_2945_);
lean_closure_set(v___f_2962_, 7, v_body_2957_);
v___x_2963_ = lean_expr_instantiate_rev(v_type_2955_, v_fvars_2946_);
lean_dec_ref(v_type_2955_);
v___x_2964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2940_, v_post_2941_, v_usedLetOnly_2942_, v_skipConstInApp_2943_, v_skipInstances_2944_, v_postApp_2945_, v___x_2963_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2966_ = lean_expr_instantiate_rev(v_value_2956_, v_fvars_2946_);
lean_dec_ref(v_fvars_2946_);
lean_dec_ref(v_value_2956_);
v___x_2967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2940_, v_post_2941_, v_usedLetOnly_2942_, v_skipConstInApp_2943_, v_skipInstances_2944_, v_postApp_2945_, v___x_2966_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = 0;
v___x_2970_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2954_, v_a_2965_, v_a_2968_, v___f_2962_, v_nondep_2958_, v___x_2969_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2970_;
}
else
{
lean_dec(v_a_2965_);
lean_dec_ref(v___f_2962_);
lean_dec(v_declName_2954_);
return v___x_2967_;
}
}
else
{
lean_dec_ref(v___f_2962_);
lean_dec_ref(v_value_2956_);
lean_dec(v_declName_2954_);
lean_dec_ref(v_fvars_2946_);
lean_dec_ref(v_postApp_2945_);
lean_dec_ref(v_post_2941_);
lean_dec_ref(v_pre_2940_);
return v___x_2964_;
}
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_expr_instantiate_rev(v_e_2947_, v_fvars_2946_);
lean_dec_ref(v_e_2947_);
lean_inc_ref(v_postApp_2945_);
lean_inc_ref(v_post_2941_);
lean_inc_ref(v_pre_2940_);
v___x_2972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2940_, v_post_2941_, v_usedLetOnly_2942_, v_skipConstInApp_2943_, v_skipInstances_2944_, v_postApp_2945_, v___x_2971_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; uint8_t v___x_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = 0;
v___x_2975_ = 1;
v___x_2976_ = l_Lean_Meta_mkLetFVars(v_fvars_2946_, v_a_2973_, v_usedLetOnly_2942_, v___x_2974_, v___x_2975_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec_ref(v_fvars_2946_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
v___x_2978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_2940_, v_post_2941_, v_usedLetOnly_2942_, v_skipConstInApp_2943_, v_skipInstances_2944_, v_postApp_2945_, v_a_2977_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2978_;
}
else
{
lean_dec_ref(v_postApp_2945_);
lean_dec_ref(v_post_2941_);
lean_dec_ref(v_pre_2940_);
return v___x_2976_;
}
}
else
{
lean_dec_ref(v_fvars_2946_);
lean_dec_ref(v_postApp_2945_);
lean_dec_ref(v_post_2941_);
lean_dec_ref(v_pre_2940_);
return v___x_2972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2979_, lean_object* v_post_2980_, uint8_t v_usedLetOnly_2981_, uint8_t v_skipConstInApp_2982_, uint8_t v_skipInstances_2983_, lean_object* v_postApp_2984_, size_t v_sz_2985_, size_t v_i_2986_, lean_object* v_bs_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v___x_2994_; 
v___x_2994_ = lean_usize_dec_lt(v_i_2986_, v_sz_2985_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; 
lean_dec_ref(v_postApp_2984_);
lean_dec_ref(v_post_2980_);
lean_dec_ref(v_pre_2979_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v_bs_2987_);
return v___x_2995_;
}
else
{
lean_object* v_v_2996_; lean_object* v___x_2997_; lean_object* v_bs_x27_2998_; lean_object* v___x_2999_; 
v_v_2996_ = lean_array_uget(v_bs_2987_, v_i_2986_);
v___x_2997_ = lean_unsigned_to_nat(0u);
v_bs_x27_2998_ = lean_array_uset(v_bs_2987_, v_i_2986_, v___x_2997_);
lean_inc_ref(v_postApp_2984_);
lean_inc_ref(v_post_2980_);
lean_inc_ref(v_pre_2979_);
v___x_2999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2979_, v_post_2980_, v_usedLetOnly_2981_, v_skipConstInApp_2982_, v_skipInstances_2983_, v_postApp_2984_, v_v_2996_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; size_t v___x_3001_; size_t v___x_3002_; lean_object* v___x_3003_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = ((size_t)1ULL);
v___x_3002_ = lean_usize_add(v_i_2986_, v___x_3001_);
v___x_3003_ = lean_array_uset(v_bs_x27_2998_, v_i_2986_, v_a_3000_);
v_i_2986_ = v___x_3002_;
v_bs_2987_ = v___x_3003_;
goto _start;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_bs_x27_2998_);
lean_dec_ref(v_postApp_2984_);
lean_dec_ref(v_post_2980_);
lean_dec_ref(v_pre_2979_);
v_a_3005_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2999_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2999_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0(lean_object* v_pre_3013_, lean_object* v_post_3014_, uint8_t v_usedLetOnly_3015_, uint8_t v_skipConstInApp_3016_, uint8_t v_skipInstances_3017_, lean_object* v_postApp_3018_, lean_object* v___x_3019_, lean_object* v___y_3020_, lean_object* v_b_3021_, lean_object* v_a_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3013_, v_post_3014_, v_usedLetOnly_3015_, v_skipConstInApp_3016_, v_skipInstances_3017_, v_postApp_3018_, v___x_3019_, v___y_3020_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3038_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3038_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3038_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3033_ = lean_array_fset(v_b_3021_, v_a_3022_, v_a_3029_);
v___x_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3034_);
v___x_3036_ = v___x_3031_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_b_3021_);
v_a_3039_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3028_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3028_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed(lean_object* v_pre_3047_, lean_object* v_post_3048_, lean_object* v_usedLetOnly_3049_, lean_object* v_skipConstInApp_3050_, lean_object* v_skipInstances_3051_, lean_object* v_postApp_3052_, lean_object* v___x_3053_, lean_object* v___y_3054_, lean_object* v_b_3055_, lean_object* v_a_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v_usedLetOnly_boxed_3062_; uint8_t v_skipConstInApp_boxed_3063_; uint8_t v_skipInstances_boxed_3064_; lean_object* v_res_3065_; 
v_usedLetOnly_boxed_3062_ = lean_unbox(v_usedLetOnly_3049_);
v_skipConstInApp_boxed_3063_ = lean_unbox(v_skipConstInApp_3050_);
v_skipInstances_boxed_3064_ = lean_unbox(v_skipInstances_3051_);
v_res_3065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0(v_pre_3047_, v_post_3048_, v_usedLetOnly_boxed_3062_, v_skipConstInApp_boxed_3063_, v_skipInstances_boxed_3064_, v_postApp_3052_, v___x_3053_, v___y_3054_, v_b_3055_, v_a_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v_a_3056_);
lean_dec(v___y_3054_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_upperBound_3066_, lean_object* v___x_3067_, lean_object* v_pre_3068_, lean_object* v_post_3069_, uint8_t v_usedLetOnly_3070_, uint8_t v_skipConstInApp_3071_, uint8_t v_skipInstances_3072_, lean_object* v_postApp_3073_, lean_object* v_a_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___y_3083_; uint8_t v___x_3106_; 
v___x_3106_ = lean_nat_dec_lt(v_a_3074_, v_upperBound_3066_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_postApp_3073_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_b_3075_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3108_ = lean_array_fget_borrowed(v_b_3075_, v_a_3074_);
v___x_3109_ = lean_array_get_size(v___x_3067_);
v___x_3110_ = lean_nat_dec_lt(v_a_3074_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___f_3114_; 
lean_inc(v___x_3108_);
v___x_3111_ = lean_box(v_usedLetOnly_3070_);
v___x_3112_ = lean_box(v_skipConstInApp_3071_);
v___x_3113_ = lean_box(v_skipInstances_3072_);
lean_inc(v_a_3074_);
lean_inc(v___y_3076_);
lean_inc_ref(v_postApp_3073_);
lean_inc_ref(v_post_3069_);
lean_inc_ref(v_pre_3068_);
v___f_3114_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3114_, 0, v_pre_3068_);
lean_closure_set(v___f_3114_, 1, v_post_3069_);
lean_closure_set(v___f_3114_, 2, v___x_3111_);
lean_closure_set(v___f_3114_, 3, v___x_3112_);
lean_closure_set(v___f_3114_, 4, v___x_3113_);
lean_closure_set(v___f_3114_, 5, v_postApp_3073_);
lean_closure_set(v___f_3114_, 6, v___x_3108_);
lean_closure_set(v___f_3114_, 7, v___y_3076_);
lean_closure_set(v___f_3114_, 8, v_b_3075_);
lean_closure_set(v___f_3114_, 9, v_a_3074_);
v___y_3083_ = v___f_3114_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3115_; uint8_t v_isInstance_3116_; 
v___x_3115_ = lean_array_fget_borrowed(v___x_3067_, v_a_3074_);
v_isInstance_3116_ = lean_ctor_get_uint8(v___x_3115_, sizeof(void*)*1 + 4);
if (v_isInstance_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___f_3120_; 
lean_inc(v___x_3108_);
v___x_3117_ = lean_box(v_usedLetOnly_3070_);
v___x_3118_ = lean_box(v_skipConstInApp_3071_);
v___x_3119_ = lean_box(v_skipInstances_3072_);
lean_inc(v_a_3074_);
lean_inc(v___y_3076_);
lean_inc_ref(v_postApp_3073_);
lean_inc_ref(v_post_3069_);
lean_inc_ref(v_pre_3068_);
v___f_3120_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_3120_, 0, v_pre_3068_);
lean_closure_set(v___f_3120_, 1, v_post_3069_);
lean_closure_set(v___f_3120_, 2, v___x_3117_);
lean_closure_set(v___f_3120_, 3, v___x_3118_);
lean_closure_set(v___f_3120_, 4, v___x_3119_);
lean_closure_set(v___f_3120_, 5, v_postApp_3073_);
lean_closure_set(v___f_3120_, 6, v___x_3108_);
lean_closure_set(v___f_3120_, 7, v___y_3076_);
lean_closure_set(v___f_3120_, 8, v_b_3075_);
lean_closure_set(v___f_3120_, 9, v_a_3074_);
v___y_3083_ = v___f_3120_;
goto v___jp_3082_;
}
else
{
lean_object* v___x_3121_; lean_object* v___f_3122_; 
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_b_3075_);
v___f_3122_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3122_, 0, v___x_3121_);
v___y_3083_ = v___f_3122_;
goto v___jp_3082_;
}
}
}
v___jp_3082_:
{
lean_object* v___x_3084_; 
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
v___x_3084_ = lean_apply_5(v___y_3083_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, lean_box(0));
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3097_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3097_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3097_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
if (lean_obj_tag(v_a_3085_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_postApp_3073_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v_a_3089_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v_a_3085_, 1);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v_a_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_del_object(v___x_3087_);
v_a_3093_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v_a_3085_, 1);
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_add(v_a_3074_, v___x_3094_);
lean_dec(v_a_3074_);
v_a_3074_ = v___x_3095_;
v_b_3075_ = v_a_3093_;
goto _start;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_postApp_3073_);
lean_dec_ref(v_post_3069_);
lean_dec_ref(v_pre_3068_);
v_a_3098_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3084_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3084_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3123_, lean_object* v_pre_3124_, lean_object* v_post_3125_, uint8_t v_usedLetOnly_3126_, uint8_t v_skipConstInApp_3127_, lean_object* v_postApp_3128_, lean_object* v___y_3129_, lean_object* v_x_3130_, lean_object* v_x_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_f_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; 
if (lean_obj_tag(v_x_3130_) == 5)
{
lean_object* v_fn_3192_; lean_object* v_arg_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_fn_3192_ = lean_ctor_get(v_x_3130_, 0);
lean_inc_ref(v_fn_3192_);
v_arg_3193_ = lean_ctor_get(v_x_3130_, 1);
lean_inc_ref(v_arg_3193_);
lean_dec_ref_known(v_x_3130_, 2);
v___x_3194_ = lean_array_set(v_x_3131_, v_x_3132_, v_arg_3193_);
v___x_3195_ = lean_unsigned_to_nat(1u);
v___x_3196_ = lean_nat_sub(v_x_3132_, v___x_3195_);
lean_dec(v_x_3132_);
v_x_3130_ = v_fn_3192_;
v_x_3131_ = v___x_3194_;
v_x_3132_ = v___x_3196_;
goto _start;
}
else
{
lean_dec(v_x_3132_);
if (v_skipConstInApp_3127_ == 0)
{
goto v___jp_3189_;
}
else
{
uint8_t v___x_3198_; 
v___x_3198_ = l_Lean_Expr_isConst(v_x_3130_);
if (v___x_3198_ == 0)
{
goto v___jp_3189_;
}
else
{
v_f_3140_ = v_x_3130_;
v___y_3141_ = v___y_3133_;
v___y_3142_ = v___y_3134_;
v___y_3143_ = v___y_3135_;
v___y_3144_ = v___y_3136_;
v___y_3145_ = v___y_3137_;
goto v___jp_3139_;
}
}
}
v___jp_3139_:
{
if (v_skipInstances_3123_ == 0)
{
size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v_sz_3146_ = lean_array_size(v_x_3131_);
v___x_3147_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_3128_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3123_, v_postApp_3128_, v_sz_3146_, v___x_3147_, v_x_3131_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = l_Lean_mkAppN(v_f_3140_, v_a_3149_);
lean_dec(v_a_3149_);
lean_inc_ref(v_postApp_3128_);
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
v___x_3151_ = lean_apply_7(v_postApp_3128_, v___y_3129_, v___x_3150_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, lean_box(0));
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3123_, v_postApp_3128_, v_a_3152_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3153_;
}
else
{
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
return v___x_3151_;
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v_f_3140_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
v_a_3154_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3148_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3148_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_array_get_size(v_x_3131_);
lean_inc_ref(v_f_3140_);
v___x_3163_ = l_Lean_Meta_getFunInfoNArgs(v_f_3140_, v___x_3162_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_paramInfo_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v_paramInfo_3165_ = lean_ctor_get(v_a_3164_, 0);
lean_inc_ref(v_paramInfo_3165_);
lean_dec(v_a_3164_);
v___x_3166_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_3128_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
v___x_3167_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v___x_3162_, v_paramInfo_3165_, v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3123_, v_postApp_3128_, v___x_3166_, v_x_3131_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec_ref(v_paramInfo_3165_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v___x_3169_ = l_Lean_mkAppN(v_f_3140_, v_a_3168_);
lean_dec(v_a_3168_);
lean_inc_ref(v_postApp_3128_);
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
v___x_3170_ = lean_apply_7(v_postApp_3128_, v___y_3129_, v___x_3169_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, lean_box(0));
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___x_3172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3123_, v_postApp_3128_, v_a_3171_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3172_;
}
else
{
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
return v___x_3170_;
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec_ref(v_f_3140_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
v_a_3173_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3167_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3167_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v_f_3140_);
lean_dec_ref(v_x_3131_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
v_a_3181_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3163_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3163_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
v___jp_3189_:
{
lean_object* v___x_3190_; 
lean_inc_ref(v_postApp_3128_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
v___x_3190_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3123_, v_postApp_3128_, v_x_3130_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v_f_3140_ = v_a_3191_;
v___y_3141_ = v___y_3133_;
v___y_3142_ = v___y_3134_;
v___y_3143_ = v___y_3135_;
v___y_3144_ = v___y_3136_;
v___y_3145_ = v___y_3137_;
goto v___jp_3139_;
}
else
{
lean_dec_ref(v_x_3131_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_postApp_3128_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
return v___x_3190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3199_, lean_object* v_pre_3200_, lean_object* v_e_3201_, lean_object* v_post_3202_, uint8_t v_usedLetOnly_3203_, uint8_t v_skipConstInApp_3204_, uint8_t v_skipInstances_3205_, lean_object* v_postApp_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Core_checkSystem(v___x_3199_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref_known(v___x_3213_, 1);
lean_inc_ref(v_pre_3200_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v_e_3201_);
v___x_3214_ = lean_apply_6(v_pre_3200_, v_e_3201_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, lean_box(0));
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3263_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3263_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3263_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___y_3220_; 
switch(lean_obj_tag(v_a_3215_))
{
case 0:
{
lean_object* v_e_3255_; lean_object* v___x_3257_; 
lean_dec_ref(v_postApp_3206_);
lean_dec_ref(v_post_3202_);
lean_dec_ref(v_e_3201_);
lean_dec_ref(v_pre_3200_);
v_e_3255_ = lean_ctor_get(v_a_3215_, 0);
lean_inc_ref(v_e_3255_);
lean_dec_ref_known(v_a_3215_, 1);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v_e_3255_);
v___x_3257_ = v___x_3217_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_e_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
case 1:
{
lean_object* v_e_3259_; lean_object* v___x_3260_; 
lean_del_object(v___x_3217_);
lean_dec_ref(v_e_3201_);
v_e_3259_ = lean_ctor_get(v_a_3215_, 0);
lean_inc_ref(v_e_3259_);
lean_dec_ref_known(v_a_3215_, 1);
v___x_3260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v_e_3259_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3260_;
}
default: 
{
lean_object* v_e_x3f_3261_; 
lean_del_object(v___x_3217_);
v_e_x3f_3261_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_e_x3f_3261_);
lean_dec_ref_known(v_a_3215_, 1);
if (lean_obj_tag(v_e_x3f_3261_) == 0)
{
v___y_3220_ = v_e_3201_;
goto v___jp_3219_;
}
else
{
lean_object* v_val_3262_; 
lean_dec_ref(v_e_3201_);
v_val_3262_ = lean_ctor_get(v_e_x3f_3261_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v_e_x3f_3261_, 1);
v___y_3220_ = v_val_3262_;
goto v___jp_3219_;
}
}
}
v___jp_3219_:
{
switch(lean_obj_tag(v___y_3220_))
{
case 7:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___x_3221_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3222_;
}
case 6:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___x_3223_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3224_;
}
case 8:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___x_3225_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3226_;
}
case 5:
{
lean_object* v_dummy_3227_; lean_object* v_nargs_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_dummy_3227_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3228_ = l_Lean_Expr_getAppNumArgs(v___y_3220_);
lean_inc(v_nargs_3228_);
v___x_3229_ = lean_mk_array(v_nargs_3228_, v_dummy_3227_);
v___x_3230_ = lean_unsigned_to_nat(1u);
v___x_3231_ = lean_nat_sub(v_nargs_3228_, v___x_3230_);
lean_dec(v_nargs_3228_);
lean_inc_ref(v___y_3220_);
v___x_3232_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3205_, v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_postApp_3206_, v___y_3220_, v___y_3220_, v___x_3229_, v___x_3231_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3232_;
}
case 10:
{
lean_object* v_data_3233_; lean_object* v_expr_3234_; lean_object* v___x_3235_; 
v_data_3233_ = lean_ctor_get(v___y_3220_, 0);
v_expr_3234_ = lean_ctor_get(v___y_3220_, 1);
lean_inc_ref(v_expr_3234_);
lean_inc_ref(v_postApp_3206_);
lean_inc_ref(v_post_3202_);
lean_inc_ref(v_pre_3200_);
v___x_3235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v_expr_3234_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; size_t v___x_3237_; size_t v___x_3238_; uint8_t v___x_3239_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = lean_ptr_addr(v_expr_3234_);
v___x_3238_ = lean_ptr_addr(v_a_3236_);
v___x_3239_ = lean_usize_dec_eq(v___x_3237_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
lean_inc(v_data_3233_);
lean_dec_ref_known(v___y_3220_, 2);
v___x_3240_ = l_Lean_Expr_mdata___override(v_data_3233_, v_a_3236_);
v___x_3241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___x_3240_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_a_3236_);
v___x_3242_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3242_;
}
}
else
{
lean_dec_ref_known(v___y_3220_, 2);
lean_dec_ref(v_postApp_3206_);
lean_dec_ref(v_post_3202_);
lean_dec_ref(v_pre_3200_);
return v___x_3235_;
}
}
case 11:
{
lean_object* v_typeName_3243_; lean_object* v_idx_3244_; lean_object* v_struct_3245_; lean_object* v___x_3246_; 
v_typeName_3243_ = lean_ctor_get(v___y_3220_, 0);
v_idx_3244_ = lean_ctor_get(v___y_3220_, 1);
v_struct_3245_ = lean_ctor_get(v___y_3220_, 2);
lean_inc_ref(v_struct_3245_);
lean_inc_ref(v_postApp_3206_);
lean_inc_ref(v_post_3202_);
lean_inc_ref(v_pre_3200_);
v___x_3246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v_struct_3245_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; size_t v___x_3248_; size_t v___x_3249_; uint8_t v___x_3250_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = lean_ptr_addr(v_struct_3245_);
v___x_3249_ = lean_ptr_addr(v_a_3247_);
v___x_3250_ = lean_usize_dec_eq(v___x_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_inc(v_idx_3244_);
lean_inc(v_typeName_3243_);
lean_dec_ref_known(v___y_3220_, 3);
v___x_3251_ = l_Lean_Expr_proj___override(v_typeName_3243_, v_idx_3244_, v_a_3247_);
v___x_3252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___x_3251_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; 
lean_dec(v_a_3247_);
v___x_3253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3253_;
}
}
else
{
lean_dec_ref_known(v___y_3220_, 3);
lean_dec_ref(v_postApp_3206_);
lean_dec_ref(v_post_3202_);
lean_dec_ref(v_pre_3200_);
return v___x_3246_;
}
}
default: 
{
lean_object* v___x_3254_; 
v___x_3254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3200_, v_post_3202_, v_usedLetOnly_3203_, v_skipConstInApp_3204_, v_skipInstances_3205_, v_postApp_3206_, v___y_3220_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3254_;
}
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_postApp_3206_);
lean_dec_ref(v_post_3202_);
lean_dec_ref(v_e_3201_);
lean_dec_ref(v_pre_3200_);
v_a_3264_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3214_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3214_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v_postApp_3206_);
lean_dec_ref(v_post_3202_);
lean_dec_ref(v_e_3201_);
lean_dec_ref(v_pre_3200_);
v_a_3272_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3213_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3213_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3280_, lean_object* v_pre_3281_, lean_object* v_e_3282_, lean_object* v_post_3283_, lean_object* v_usedLetOnly_3284_, lean_object* v_skipConstInApp_3285_, lean_object* v_skipInstances_3286_, lean_object* v_postApp_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v_usedLetOnly_boxed_3294_; uint8_t v_skipConstInApp_boxed_3295_; uint8_t v_skipInstances_boxed_3296_; lean_object* v_res_3297_; 
v_usedLetOnly_boxed_3294_ = lean_unbox(v_usedLetOnly_3284_);
v_skipConstInApp_boxed_3295_ = lean_unbox(v_skipConstInApp_3285_);
v_skipInstances_boxed_3296_ = lean_unbox(v_skipInstances_3286_);
v_res_3297_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3280_, v_pre_3281_, v_e_3282_, v_post_3283_, v_usedLetOnly_boxed_3294_, v_skipConstInApp_boxed_3295_, v_skipInstances_boxed_3296_, v_postApp_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3298_, lean_object* v_post_3299_, uint8_t v_usedLetOnly_3300_, uint8_t v_skipConstInApp_3301_, uint8_t v_skipInstances_3302_, lean_object* v_postApp_3303_, lean_object* v_e_3304_, lean_object* v_a_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
lean_inc(v_a_3305_);
v___x_3311_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3311_, 0, lean_box(0));
lean_closure_set(v___x_3311_, 1, lean_box(0));
lean_closure_set(v___x_3311_, 2, v_a_3305_);
v___x_3312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3311_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3347_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3347_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3347_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_a_3313_, v_e_3304_);
lean_dec(v_a_3313_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___f_3322_; lean_object* v___x_3323_; 
lean_del_object(v___x_3315_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3319_ = lean_box(v_usedLetOnly_3300_);
v___x_3320_ = lean_box(v_skipConstInApp_3301_);
v___x_3321_ = lean_box(v_skipInstances_3302_);
lean_inc_ref(v_e_3304_);
v___f_3322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 14, 8);
lean_closure_set(v___f_3322_, 0, v___x_3318_);
lean_closure_set(v___f_3322_, 1, v_pre_3298_);
lean_closure_set(v___f_3322_, 2, v_e_3304_);
lean_closure_set(v___f_3322_, 3, v_post_3299_);
lean_closure_set(v___f_3322_, 4, v___x_3319_);
lean_closure_set(v___f_3322_, 5, v___x_3320_);
lean_closure_set(v___f_3322_, 6, v___x_3321_);
lean_closure_set(v___f_3322_, 7, v_postApp_3303_);
v___x_3323_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3322_, v_a_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___f_3325_; lean_object* v___x_3326_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc_n(v_a_3324_, 2);
lean_dec_ref_known(v___x_3323_, 1);
lean_inc(v_a_3305_);
v___f_3325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3325_, 0, v_a_3305_);
lean_closure_set(v___f_3325_, 1, v_e_3304_);
lean_closure_set(v___f_3325_, 2, v_a_3324_);
v___x_3326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3325_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3334_);
v___x_3328_ = v___x_3326_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_dec(v___x_3326_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v_a_3324_);
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3324_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3324_);
v_a_3335_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3326_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3326_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_dec_ref(v_e_3304_);
return v___x_3323_;
}
}
else
{
lean_object* v_val_3343_; lean_object* v___x_3345_; 
lean_dec_ref(v_e_3304_);
lean_dec_ref(v_postApp_3303_);
lean_dec_ref(v_post_3299_);
lean_dec_ref(v_pre_3298_);
v_val_3343_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3317_, 1);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v_val_3343_);
v___x_3345_ = v___x_3315_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_val_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v_e_3304_);
lean_dec_ref(v_postApp_3303_);
lean_dec_ref(v_post_3299_);
lean_dec_ref(v_pre_3298_);
v_a_3348_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3312_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3312_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3356_, lean_object* v_post_3357_, uint8_t v_usedLetOnly_3358_, uint8_t v_skipConstInApp_3359_, uint8_t v_skipInstances_3360_, lean_object* v_postApp_3361_, lean_object* v_fvars_3362_, lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
if (lean_obj_tag(v_e_3363_) == 7)
{
lean_object* v_binderName_3370_; lean_object* v_binderType_3371_; lean_object* v_body_3372_; uint8_t v_binderInfo_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___f_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_binderName_3370_ = lean_ctor_get(v_e_3363_, 0);
lean_inc(v_binderName_3370_);
v_binderType_3371_ = lean_ctor_get(v_e_3363_, 1);
lean_inc_ref(v_binderType_3371_);
v_body_3372_ = lean_ctor_get(v_e_3363_, 2);
lean_inc_ref(v_body_3372_);
v_binderInfo_3373_ = lean_ctor_get_uint8(v_e_3363_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3363_, 3);
v___x_3374_ = lean_box(v_usedLetOnly_3358_);
v___x_3375_ = lean_box(v_skipConstInApp_3359_);
v___x_3376_ = lean_box(v_skipInstances_3360_);
lean_inc_ref(v_postApp_3361_);
lean_inc_ref(v_post_3357_);
lean_inc_ref(v_pre_3356_);
lean_inc_ref(v_fvars_3362_);
v___f_3377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3377_, 0, v_fvars_3362_);
lean_closure_set(v___f_3377_, 1, v_pre_3356_);
lean_closure_set(v___f_3377_, 2, v_post_3357_);
lean_closure_set(v___f_3377_, 3, v___x_3374_);
lean_closure_set(v___f_3377_, 4, v___x_3375_);
lean_closure_set(v___f_3377_, 5, v___x_3376_);
lean_closure_set(v___f_3377_, 6, v_postApp_3361_);
lean_closure_set(v___f_3377_, 7, v_body_3372_);
v___x_3378_ = lean_expr_instantiate_rev(v_binderType_3371_, v_fvars_3362_);
lean_dec_ref(v_fvars_3362_);
lean_dec_ref(v_binderType_3371_);
v___x_3379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v_postApp_3361_, v___x_3378_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = 0;
v___x_3382_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3370_, v_binderInfo_3373_, v_a_3380_, v___f_3377_, v___x_3381_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3382_;
}
else
{
lean_dec_ref(v___f_3377_);
lean_dec(v_binderName_3370_);
return v___x_3379_;
}
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = lean_expr_instantiate_rev(v_e_3363_, v_fvars_3362_);
lean_dec_ref(v_e_3363_);
lean_inc_ref(v_postApp_3361_);
lean_inc_ref(v_post_3357_);
lean_inc_ref(v_pre_3356_);
v___x_3384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v_postApp_3361_, v___x_3383_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; uint8_t v___x_3386_; uint8_t v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = 0;
v___x_3387_ = 1;
v___x_3388_ = 1;
v___x_3389_ = l_Lean_Meta_mkForallFVars(v_fvars_3362_, v_a_3385_, v___x_3386_, v_usedLetOnly_3358_, v___x_3387_, v___x_3388_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec_ref(v_fvars_3362_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v_postApp_3361_, v_a_3390_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3391_;
}
else
{
lean_dec_ref(v_postApp_3361_);
lean_dec_ref(v_post_3357_);
lean_dec_ref(v_pre_3356_);
return v___x_3389_;
}
}
else
{
lean_dec_ref(v_fvars_3362_);
lean_dec_ref(v_postApp_3361_);
lean_dec_ref(v_post_3357_);
lean_dec_ref(v_pre_3356_);
return v___x_3384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3392_, lean_object* v_pre_3393_, lean_object* v_post_3394_, uint8_t v_usedLetOnly_3395_, uint8_t v_skipConstInApp_3396_, uint8_t v_skipInstances_3397_, lean_object* v_postApp_3398_, lean_object* v_body_3399_, lean_object* v_x_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = lean_array_push(v_fvars_3392_, v_x_3400_);
v___x_3408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3393_, v_post_3394_, v_usedLetOnly_3395_, v_skipConstInApp_3396_, v_skipInstances_3397_, v_postApp_3398_, v___x_3407_, v_body_3399_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_3409_, lean_object* v_post_3410_, lean_object* v_usedLetOnly_3411_, lean_object* v_skipConstInApp_3412_, lean_object* v_skipInstances_3413_, lean_object* v_postApp_3414_, lean_object* v_e_3415_, lean_object* v_a_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
uint8_t v_usedLetOnly_boxed_3422_; uint8_t v_skipConstInApp_boxed_3423_; uint8_t v_skipInstances_boxed_3424_; lean_object* v_res_3425_; 
v_usedLetOnly_boxed_3422_ = lean_unbox(v_usedLetOnly_3411_);
v_skipConstInApp_boxed_3423_ = lean_unbox(v_skipConstInApp_3412_);
v_skipInstances_boxed_3424_ = lean_unbox(v_skipInstances_3413_);
v_res_3425_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_pre_3409_, v_post_3410_, v_usedLetOnly_boxed_3422_, v_skipConstInApp_boxed_3423_, v_skipInstances_boxed_3424_, v_postApp_3414_, v_e_3415_, v_a_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v_a_3416_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3426_, lean_object* v_post_3427_, lean_object* v_usedLetOnly_3428_, lean_object* v_skipConstInApp_3429_, lean_object* v_skipInstances_3430_, lean_object* v_postApp_3431_, lean_object* v_sz_3432_, lean_object* v_i_3433_, lean_object* v_bs_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v_usedLetOnly_boxed_3441_; uint8_t v_skipConstInApp_boxed_3442_; uint8_t v_skipInstances_boxed_3443_; size_t v_sz_boxed_3444_; size_t v_i_boxed_3445_; lean_object* v_res_3446_; 
v_usedLetOnly_boxed_3441_ = lean_unbox(v_usedLetOnly_3428_);
v_skipConstInApp_boxed_3442_ = lean_unbox(v_skipConstInApp_3429_);
v_skipInstances_boxed_3443_ = lean_unbox(v_skipInstances_3430_);
v_sz_boxed_3444_ = lean_unbox_usize(v_sz_3432_);
lean_dec(v_sz_3432_);
v_i_boxed_3445_ = lean_unbox_usize(v_i_3433_);
lean_dec(v_i_3433_);
v_res_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3426_, v_post_3427_, v_usedLetOnly_boxed_3441_, v_skipConstInApp_boxed_3442_, v_skipInstances_boxed_3443_, v_postApp_3431_, v_sz_boxed_3444_, v_i_boxed_3445_, v_bs_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3447_, lean_object* v_post_3448_, lean_object* v_usedLetOnly_3449_, lean_object* v_skipConstInApp_3450_, lean_object* v_skipInstances_3451_, lean_object* v_postApp_3452_, lean_object* v_e_3453_, lean_object* v_a_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
uint8_t v_usedLetOnly_boxed_3460_; uint8_t v_skipConstInApp_boxed_3461_; uint8_t v_skipInstances_boxed_3462_; lean_object* v_res_3463_; 
v_usedLetOnly_boxed_3460_ = lean_unbox(v_usedLetOnly_3449_);
v_skipConstInApp_boxed_3461_ = lean_unbox(v_skipConstInApp_3450_);
v_skipInstances_boxed_3462_ = lean_unbox(v_skipInstances_3451_);
v_res_3463_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3447_, v_post_3448_, v_usedLetOnly_boxed_3460_, v_skipConstInApp_boxed_3461_, v_skipInstances_boxed_3462_, v_postApp_3452_, v_e_3453_, v_a_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v_a_3454_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3464_, lean_object* v_post_3465_, lean_object* v_usedLetOnly_3466_, lean_object* v_skipConstInApp_3467_, lean_object* v_skipInstances_3468_, lean_object* v_postApp_3469_, lean_object* v_fvars_3470_, lean_object* v_e_3471_, lean_object* v_a_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v_usedLetOnly_boxed_3478_; uint8_t v_skipConstInApp_boxed_3479_; uint8_t v_skipInstances_boxed_3480_; lean_object* v_res_3481_; 
v_usedLetOnly_boxed_3478_ = lean_unbox(v_usedLetOnly_3466_);
v_skipConstInApp_boxed_3479_ = lean_unbox(v_skipConstInApp_3467_);
v_skipInstances_boxed_3480_ = lean_unbox(v_skipInstances_3468_);
v_res_3481_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3464_, v_post_3465_, v_usedLetOnly_boxed_3478_, v_skipConstInApp_boxed_3479_, v_skipInstances_boxed_3480_, v_postApp_3469_, v_fvars_3470_, v_e_3471_, v_a_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v_a_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3482_, lean_object* v_post_3483_, lean_object* v_usedLetOnly_3484_, lean_object* v_skipConstInApp_3485_, lean_object* v_skipInstances_3486_, lean_object* v_postApp_3487_, lean_object* v_fvars_3488_, lean_object* v_e_3489_, lean_object* v_a_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v_usedLetOnly_boxed_3496_; uint8_t v_skipConstInApp_boxed_3497_; uint8_t v_skipInstances_boxed_3498_; lean_object* v_res_3499_; 
v_usedLetOnly_boxed_3496_ = lean_unbox(v_usedLetOnly_3484_);
v_skipConstInApp_boxed_3497_ = lean_unbox(v_skipConstInApp_3485_);
v_skipInstances_boxed_3498_ = lean_unbox(v_skipInstances_3486_);
v_res_3499_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3482_, v_post_3483_, v_usedLetOnly_boxed_3496_, v_skipConstInApp_boxed_3497_, v_skipInstances_boxed_3498_, v_postApp_3487_, v_fvars_3488_, v_e_3489_, v_a_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v_a_3490_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3500_, lean_object* v_post_3501_, lean_object* v_usedLetOnly_3502_, lean_object* v_skipConstInApp_3503_, lean_object* v_skipInstances_3504_, lean_object* v_postApp_3505_, lean_object* v_fvars_3506_, lean_object* v_e_3507_, lean_object* v_a_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_usedLetOnly_boxed_3514_; uint8_t v_skipConstInApp_boxed_3515_; uint8_t v_skipInstances_boxed_3516_; lean_object* v_res_3517_; 
v_usedLetOnly_boxed_3514_ = lean_unbox(v_usedLetOnly_3502_);
v_skipConstInApp_boxed_3515_ = lean_unbox(v_skipConstInApp_3503_);
v_skipInstances_boxed_3516_ = lean_unbox(v_skipInstances_3504_);
v_res_3517_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3500_, v_post_3501_, v_usedLetOnly_boxed_3514_, v_skipConstInApp_boxed_3515_, v_skipInstances_boxed_3516_, v_postApp_3505_, v_fvars_3506_, v_e_3507_, v_a_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_a_3508_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_upperBound_3518_, lean_object* v___x_3519_, lean_object* v_pre_3520_, lean_object* v_post_3521_, lean_object* v_usedLetOnly_3522_, lean_object* v_skipConstInApp_3523_, lean_object* v_skipInstances_3524_, lean_object* v_postApp_3525_, lean_object* v_a_3526_, lean_object* v_b_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
uint8_t v_usedLetOnly_boxed_3534_; uint8_t v_skipConstInApp_boxed_3535_; uint8_t v_skipInstances_boxed_3536_; lean_object* v_res_3537_; 
v_usedLetOnly_boxed_3534_ = lean_unbox(v_usedLetOnly_3522_);
v_skipConstInApp_boxed_3535_ = lean_unbox(v_skipConstInApp_3523_);
v_skipInstances_boxed_3536_ = lean_unbox(v_skipInstances_3524_);
v_res_3537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_upperBound_3518_, v___x_3519_, v_pre_3520_, v_post_3521_, v_usedLetOnly_boxed_3534_, v_skipConstInApp_boxed_3535_, v_skipInstances_boxed_3536_, v_postApp_3525_, v_a_3526_, v_b_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___x_3519_);
lean_dec(v_upperBound_3518_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3538_, lean_object* v_pre_3539_, lean_object* v_post_3540_, lean_object* v_usedLetOnly_3541_, lean_object* v_skipConstInApp_3542_, lean_object* v_postApp_3543_, lean_object* v___y_3544_, lean_object* v_x_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v_skipInstances_boxed_3554_; uint8_t v_usedLetOnly_boxed_3555_; uint8_t v_skipConstInApp_boxed_3556_; lean_object* v_res_3557_; 
v_skipInstances_boxed_3554_ = lean_unbox(v_skipInstances_3538_);
v_usedLetOnly_boxed_3555_ = lean_unbox(v_usedLetOnly_3541_);
v_skipConstInApp_boxed_3556_ = lean_unbox(v_skipConstInApp_3542_);
v_res_3557_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3554_, v_pre_3539_, v_post_3540_, v_usedLetOnly_boxed_3555_, v_skipConstInApp_boxed_3556_, v_postApp_3543_, v___y_3544_, v_x_3545_, v_x_3546_, v_x_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
return v_res_3557_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = lean_box(0);
v___x_3560_ = lean_unsigned_to_nat(16u);
v___x_3561_ = lean_mk_array(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3563_ = lean_unsigned_to_nat(0u);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v___x_3562_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3566_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3566_, 0, lean_box(0));
lean_closure_set(v___x_3566_, 1, lean_box(0));
lean_closure_set(v___x_3566_, 2, v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3567_, lean_object* v_pre_3568_, lean_object* v_post_3569_, uint8_t v_usedLetOnly_3570_, uint8_t v_skipConstInApp_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___f_3577_; uint8_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v_a_3581_; lean_object* v___x_3582_; 
v___f_3577_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0));
v___x_3578_ = 0;
v___x_3579_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__3);
v___x_3580_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3579_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3568_, v_post_3569_, v_usedLetOnly_3570_, v_skipConstInApp_3571_, v___x_3578_, v___f_3577_, v_input_3567_, v_a_3581_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3584_, 0, lean_box(0));
lean_closure_set(v___x_3584_, 1, lean_box(0));
lean_closure_set(v___x_3584_, 2, v_a_3581_);
v___x_3585_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3584_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; 
v_unused_3593_ = lean_ctor_get(v___x_3585_, 0);
lean_dec(v_unused_3593_);
v___x_3587_ = v___x_3585_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_dec(v___x_3585_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v_a_3583_);
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3583_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
else
{
lean_dec(v_a_3581_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3594_, lean_object* v_pre_3595_, lean_object* v_post_3596_, lean_object* v_usedLetOnly_3597_, lean_object* v_skipConstInApp_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
uint8_t v_usedLetOnly_boxed_3604_; uint8_t v_skipConstInApp_boxed_3605_; lean_object* v_res_3606_; 
v_usedLetOnly_boxed_3604_ = lean_unbox(v_usedLetOnly_3597_);
v_skipConstInApp_boxed_3605_ = lean_unbox(v_skipConstInApp_3598_);
v_res_3606_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3594_, v_pre_3595_, v_post_3596_, v_usedLetOnly_boxed_3604_, v_skipConstInApp_boxed_3605_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3608_, lean_object* v_p_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v___f_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v_a_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; 
v___f_3615_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3616_, 0, v_p_3609_);
v___x_3617_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3608_, v_a_3611_);
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
v___x_3619_ = 0;
v___x_3620_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3618_, v___f_3615_, v___f_3616_, v___x_3619_, v___x_3619_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3621_, lean_object* v_p_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_etaStructReduce(v_e_3621_, v_p_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_3629_, lean_object* v_m_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___redArg(v_m_3630_, v_a_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_m_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_00_u03b2_3633_, v_m_3634_, v_a_3635_);
lean_dec_ref(v_a_3635_);
lean_dec_ref(v_m_3634_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_upperBound_3637_, lean_object* v___x_3638_, lean_object* v_pre_3639_, lean_object* v_post_3640_, uint8_t v_usedLetOnly_3641_, uint8_t v_skipConstInApp_3642_, uint8_t v_skipInstances_3643_, lean_object* v_postApp_3644_, lean_object* v___x_3645_, lean_object* v_inst_3646_, lean_object* v_R_3647_, lean_object* v_a_3648_, lean_object* v_b_3649_, lean_object* v_c_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_upperBound_3637_, v___x_3638_, v_pre_3639_, v_post_3640_, v_usedLetOnly_3641_, v_skipConstInApp_3642_, v_skipInstances_3643_, v_postApp_3644_, v_a_3648_, v_b_3649_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_3658_ = _args[0];
lean_object* v___x_3659_ = _args[1];
lean_object* v_pre_3660_ = _args[2];
lean_object* v_post_3661_ = _args[3];
lean_object* v_usedLetOnly_3662_ = _args[4];
lean_object* v_skipConstInApp_3663_ = _args[5];
lean_object* v_skipInstances_3664_ = _args[6];
lean_object* v_postApp_3665_ = _args[7];
lean_object* v___x_3666_ = _args[8];
lean_object* v_inst_3667_ = _args[9];
lean_object* v_R_3668_ = _args[10];
lean_object* v_a_3669_ = _args[11];
lean_object* v_b_3670_ = _args[12];
lean_object* v_c_3671_ = _args[13];
lean_object* v___y_3672_ = _args[14];
lean_object* v___y_3673_ = _args[15];
lean_object* v___y_3674_ = _args[16];
lean_object* v___y_3675_ = _args[17];
lean_object* v___y_3676_ = _args[18];
lean_object* v___y_3677_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3678_; uint8_t v_skipConstInApp_boxed_3679_; uint8_t v_skipInstances_boxed_3680_; lean_object* v_res_3681_; 
v_usedLetOnly_boxed_3678_ = lean_unbox(v_usedLetOnly_3662_);
v_skipConstInApp_boxed_3679_ = lean_unbox(v_skipConstInApp_3663_);
v_skipInstances_boxed_3680_ = lean_unbox(v_skipInstances_3664_);
v_res_3681_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_upperBound_3658_, v___x_3659_, v_pre_3660_, v_post_3661_, v_usedLetOnly_boxed_3678_, v_skipConstInApp_boxed_3679_, v_skipInstances_boxed_3680_, v_postApp_3665_, v___x_3666_, v_inst_3667_, v_R_3668_, v_a_3669_, v_b_3670_, v_c_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec(v___x_3666_);
lean_dec_ref(v___x_3659_);
lean_dec(v_upperBound_3658_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3682_, lean_object* v_name_3683_, uint8_t v_bi_3684_, lean_object* v_type_3685_, lean_object* v_k_3686_, uint8_t v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3683_, v_bi_3684_, v_type_3685_, v_k_3686_, v_kind_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3695_, lean_object* v_name_3696_, lean_object* v_bi_3697_, lean_object* v_type_3698_, lean_object* v_k_3699_, lean_object* v_kind_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_bi_boxed_3707_; uint8_t v_kind_boxed_3708_; lean_object* v_res_3709_; 
v_bi_boxed_3707_ = lean_unbox(v_bi_3697_);
v_kind_boxed_3708_ = lean_unbox(v_kind_3700_);
v_res_3709_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3695_, v_name_3696_, v_bi_boxed_3707_, v_type_3698_, v_k_3699_, v_kind_boxed_3708_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3710_, lean_object* v_name_3711_, lean_object* v_type_3712_, lean_object* v_val_3713_, lean_object* v_k_3714_, uint8_t v_nondep_3715_, uint8_t v_kind_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3711_, v_type_3712_, v_val_3713_, v_k_3714_, v_nondep_3715_, v_kind_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3724_, lean_object* v_name_3725_, lean_object* v_type_3726_, lean_object* v_val_3727_, lean_object* v_k_3728_, lean_object* v_nondep_3729_, lean_object* v_kind_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v_nondep_boxed_3737_; uint8_t v_kind_boxed_3738_; lean_object* v_res_3739_; 
v_nondep_boxed_3737_ = lean_unbox(v_nondep_3729_);
v_kind_boxed_3738_ = lean_unbox(v_kind_3730_);
v_res_3739_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3724_, v_name_3725_, v_type_3726_, v_val_3727_, v_k_3728_, v_nondep_boxed_3737_, v_kind_boxed_3738_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3740_, lean_object* v_ref_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3741_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3748_, lean_object* v_ref_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3748_, v_ref_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3765_, lean_object* v_x_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3765_, v_x_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3774_, lean_object* v_m_3775_, lean_object* v_a_3776_, lean_object* v_b_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3775_, v_a_3776_, v_b_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3779_, lean_object* v_a_3780_, lean_object* v_x_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___redArg(v_a_3780_, v_x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3783_, lean_object* v_a_3784_, lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2_spec__3(v_00_u03b2_3783_, v_a_3784_, v_x_3785_);
lean_dec(v_x_3785_);
lean_dec_ref(v_a_3784_);
return v_res_3786_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3787_, lean_object* v_a_3788_, lean_object* v_x_3789_){
_start:
{
uint8_t v___x_3790_; 
v___x_3790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3788_, v_x_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3791_, lean_object* v_a_3792_, lean_object* v_x_3793_){
_start:
{
uint8_t v_res_3794_; lean_object* v_r_3795_; 
v_res_3794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3791_, v_a_3792_, v_x_3793_);
lean_dec(v_x_3793_);
lean_dec_ref(v_a_3792_);
v_r_3795_ = lean_box(v_res_3794_);
return v_r_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3796_, lean_object* v_data_3797_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3797_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3799_, lean_object* v_a_3800_, lean_object* v_b_3801_, lean_object* v_x_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3800_, v_b_3801_, v_x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3804_, lean_object* v_i_3805_, lean_object* v_source_3806_, lean_object* v_target_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3805_, v_source_3806_, v_target_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3810_, v_x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3813_, lean_object* v_inst_3814_, lean_object* v_toBind_3815_, lean_object* v___f_3816_, lean_object* v_____do__lift_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3818_, 0, v_____do__lift_3817_);
lean_closure_set(v___x_3818_, 1, v_binderType_3813_);
v___x_3819_ = lean_apply_2(v_inst_3814_, lean_box(0), v___x_3818_);
v___x_3820_ = lean_apply_4(v_toBind_3815_, lean_box(0), lean_box(0), v___x_3819_, v___f_3816_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3821_, lean_object* v_usedFields_3822_, lean_object* v_binderName_3823_, lean_object* v_body_3824_, lean_object* v_val_3825_, lean_object* v_inst_3826_, lean_object* v_inst_3827_, lean_object* v_fieldVal_x3f_3828_, lean_object* v_____do__lift_3829_){
_start:
{
uint8_t v_____do__lift_291__boxed_3830_; lean_object* v_res_3831_; 
v_____do__lift_291__boxed_3830_ = lean_unbox(v_____do__lift_3829_);
v_res_3831_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3821_, v_usedFields_3822_, v_binderName_3823_, v_body_3824_, v_val_3825_, v_inst_3826_, v_inst_3827_, v_fieldVal_x3f_3828_, v_____do__lift_291__boxed_3830_);
lean_dec_ref(v_val_3825_);
lean_dec_ref(v_body_3824_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3832_, lean_object* v_usedFields_3833_, lean_object* v_binderName_3834_, lean_object* v_body_3835_, lean_object* v_inst_3836_, lean_object* v_inst_3837_, lean_object* v_fieldVal_x3f_3838_, lean_object* v_binderType_3839_, lean_object* v_toBind_3840_, lean_object* v_____x_3841_){
_start:
{
if (lean_obj_tag(v_____x_3841_) == 1)
{
lean_object* v_val_3842_; lean_object* v___f_3843_; lean_object* v___f_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_val_3842_ = lean_ctor_get(v_____x_3841_, 0);
lean_inc_n(v_val_3842_, 2);
lean_dec_ref_known(v_____x_3841_, 1);
lean_inc_n(v_inst_3837_, 2);
v___f_3843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3843_, 0, v_toPure_3832_);
lean_closure_set(v___f_3843_, 1, v_usedFields_3833_);
lean_closure_set(v___f_3843_, 2, v_binderName_3834_);
lean_closure_set(v___f_3843_, 3, v_body_3835_);
lean_closure_set(v___f_3843_, 4, v_val_3842_);
lean_closure_set(v___f_3843_, 5, v_inst_3836_);
lean_closure_set(v___f_3843_, 6, v_inst_3837_);
lean_closure_set(v___f_3843_, 7, v_fieldVal_x3f_3838_);
lean_inc(v_toBind_3840_);
v___f_3844_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3844_, 0, v_binderType_3839_);
lean_closure_set(v___f_3844_, 1, v_inst_3837_);
lean_closure_set(v___f_3844_, 2, v_toBind_3840_);
lean_closure_set(v___f_3844_, 3, v___f_3843_);
v___x_3845_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3845_, 0, v_val_3842_);
v___x_3846_ = lean_apply_2(v_inst_3837_, lean_box(0), v___x_3845_);
v___x_3847_ = lean_apply_4(v_toBind_3840_, lean_box(0), lean_box(0), v___x_3846_, v___f_3844_);
return v___x_3847_;
}
else
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec(v_____x_3841_);
lean_dec(v_toBind_3840_);
lean_dec_ref(v_binderType_3839_);
lean_dec(v_fieldVal_x3f_3838_);
lean_dec(v_inst_3837_);
lean_dec_ref(v_inst_3836_);
lean_dec_ref(v_body_3835_);
lean_dec(v_binderName_3834_);
lean_dec(v_usedFields_3833_);
v___x_3848_ = lean_box(0);
v___x_3849_ = lean_apply_2(v_toPure_3832_, lean_box(0), v___x_3848_);
return v___x_3849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3853_, lean_object* v_inst_3854_, lean_object* v_fieldVal_x3f_3855_, lean_object* v_usedFields_3856_, lean_object* v_e_3857_){
_start:
{
lean_object* v_toApplicative_3858_; lean_object* v_toBind_3859_; lean_object* v_toPure_3860_; 
v_toApplicative_3858_ = lean_ctor_get(v_inst_3853_, 0);
v_toBind_3859_ = lean_ctor_get(v_inst_3853_, 1);
v_toPure_3860_ = lean_ctor_get(v_toApplicative_3858_, 1);
lean_inc(v_toPure_3860_);
if (lean_obj_tag(v_e_3857_) == 6)
{
lean_object* v_binderName_3865_; lean_object* v_binderType_3866_; lean_object* v_body_3867_; lean_object* v___f_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_inc_n(v_toBind_3859_, 2);
v_binderName_3865_ = lean_ctor_get(v_e_3857_, 0);
lean_inc_n(v_binderName_3865_, 2);
v_binderType_3866_ = lean_ctor_get(v_e_3857_, 1);
lean_inc_ref(v_binderType_3866_);
v_body_3867_ = lean_ctor_get(v_e_3857_, 2);
lean_inc_ref(v_body_3867_);
lean_dec_ref_known(v_e_3857_, 3);
lean_inc(v_fieldVal_x3f_3855_);
v___f_3868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3868_, 0, v_toPure_3860_);
lean_closure_set(v___f_3868_, 1, v_usedFields_3856_);
lean_closure_set(v___f_3868_, 2, v_binderName_3865_);
lean_closure_set(v___f_3868_, 3, v_body_3867_);
lean_closure_set(v___f_3868_, 4, v_inst_3853_);
lean_closure_set(v___f_3868_, 5, v_inst_3854_);
lean_closure_set(v___f_3868_, 6, v_fieldVal_x3f_3855_);
lean_closure_set(v___f_3868_, 7, v_binderType_3866_);
lean_closure_set(v___f_3868_, 8, v_toBind_3859_);
v___x_3869_ = lean_apply_1(v_fieldVal_x3f_3855_, v_binderName_3865_);
v___x_3870_ = lean_apply_4(v_toBind_3859_, lean_box(0), lean_box(0), v___x_3869_, v___f_3868_);
return v___x_3870_;
}
else
{
lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_fieldVal_x3f_3855_);
lean_dec(v_inst_3854_);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_inst_3853_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3888_ = lean_ctor_get(v_inst_3853_, 1);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_inst_3853_, 0);
lean_dec(v_unused_3889_);
v___x_3872_ = v_inst_3853_;
v_isShared_3873_ = v_isSharedCheck_3887_;
goto v_resetjp_3871_;
}
else
{
lean_dec(v_inst_3853_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3887_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; uint8_t v___x_3875_; 
lean_inc_ref(v_e_3857_);
v___x_3874_ = l_Lean_Expr_cleanupAnnotations(v_e_3857_);
v___x_3875_ = l_Lean_Expr_isApp(v___x_3874_);
if (v___x_3875_ == 0)
{
lean_dec_ref(v___x_3874_);
lean_del_object(v___x_3872_);
goto v___jp_3861_;
}
else
{
lean_object* v_arg_3876_; lean_object* v___x_3877_; uint8_t v___x_3878_; 
v_arg_3876_ = lean_ctor_get(v___x_3874_, 1);
lean_inc_ref(v_arg_3876_);
v___x_3877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3874_);
v___x_3878_ = l_Lean_Expr_isApp(v___x_3877_);
if (v___x_3878_ == 0)
{
lean_dec_ref(v___x_3877_);
lean_dec_ref(v_arg_3876_);
lean_del_object(v___x_3872_);
goto v___jp_3861_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3877_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3881_ = l_Lean_Expr_isConstOf(v___x_3879_, v___x_3880_);
lean_dec_ref(v___x_3879_);
if (v___x_3881_ == 0)
{
lean_dec_ref(v_arg_3876_);
lean_del_object(v___x_3872_);
goto v___jp_3861_;
}
else
{
lean_object* v___x_3883_; 
lean_dec_ref(v_e_3857_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 1, v_arg_3876_);
lean_ctor_set(v___x_3872_, 0, v_usedFields_3856_);
v___x_3883_ = v___x_3872_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_usedFields_3856_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_arg_3876_);
v___x_3883_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
v___x_3885_ = lean_apply_2(v_toPure_3860_, lean_box(0), v___x_3884_);
return v___x_3885_;
}
}
}
}
}
}
v___jp_3861_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v_usedFields_3856_);
lean_ctor_set(v___x_3862_, 1, v_e_3857_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
v___x_3864_ = lean_apply_2(v_toPure_3860_, lean_box(0), v___x_3863_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3890_, lean_object* v_usedFields_3891_, lean_object* v_binderName_3892_, lean_object* v_body_3893_, lean_object* v_val_3894_, lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_fieldVal_x3f_3897_, uint8_t v_____do__lift_3898_){
_start:
{
if (v_____do__lift_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_dec(v_fieldVal_x3f_3897_);
lean_dec(v_inst_3896_);
lean_dec_ref(v_inst_3895_);
lean_dec(v_binderName_3892_);
lean_dec(v_usedFields_3891_);
v___x_3899_ = lean_box(0);
v___x_3900_ = lean_apply_2(v_toPure_3890_, lean_box(0), v___x_3899_);
return v___x_3900_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec(v_toPure_3890_);
v___x_3901_ = l_Lean_NameSet_insert(v_usedFields_3891_, v_binderName_3892_);
v___x_3902_ = lean_expr_instantiate1(v_body_3893_, v_val_3894_);
v___x_3903_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3895_, v_inst_3896_, v_fieldVal_x3f_3897_, v___x_3901_, v___x_3902_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3904_, lean_object* v_inst_3905_, lean_object* v_inst_3906_, lean_object* v_fieldVal_x3f_3907_, lean_object* v_usedFields_3908_, lean_object* v_e_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3905_, v_inst_3906_, v_fieldVal_x3f_3907_, v_usedFields_3908_, v_e_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3911_, lean_object* v_inst_3912_, lean_object* v_fieldVal_x3f_3913_, lean_object* v_toPure_3914_, lean_object* v_____s_3915_){
_start:
{
lean_object* v_fst_3916_; 
v_fst_3916_ = lean_ctor_get(v_____s_3915_, 0);
if (lean_obj_tag(v_fst_3916_) == 0)
{
lean_object* v_snd_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec(v_toPure_3914_);
v_snd_3917_ = lean_ctor_get(v_____s_3915_, 1);
lean_inc(v_snd_3917_);
lean_dec_ref(v_____s_3915_);
v___x_3918_ = l_Lean_NameSet_empty;
v___x_3919_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3911_, v_inst_3912_, v_fieldVal_x3f_3913_, v___x_3918_, v_snd_3917_);
return v___x_3919_;
}
else
{
lean_object* v_val_3920_; lean_object* v___x_3921_; 
lean_inc_ref(v_fst_3916_);
lean_dec_ref(v_____s_3915_);
lean_dec(v_fieldVal_x3f_3913_);
lean_dec(v_inst_3912_);
lean_dec_ref(v_inst_3911_);
v_val_3920_ = lean_ctor_get(v_fst_3916_, 0);
lean_inc(v_val_3920_);
lean_dec_ref_known(v_fst_3916_, 1);
v___x_3921_ = lean_apply_2(v_toPure_3914_, lean_box(0), v_val_3920_);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3922_, lean_object* v_a_3923_, lean_object* v___x_3924_, lean_object* v_toPure_3925_, lean_object* v_____r_3926_){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3927_ = lean_expr_instantiate1(v_body_3922_, v_a_3923_);
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3924_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
v___x_3930_ = lean_apply_2(v_toPure_3925_, lean_box(0), v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3931_, lean_object* v_a_3932_, lean_object* v___x_3933_, lean_object* v_toPure_3934_, lean_object* v_____r_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3931_, v_a_3932_, v___x_3933_, v_toPure_3934_, v_____r_3935_);
lean_dec_ref(v_a_3932_);
lean_dec_ref(v_body_3931_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3939_, lean_object* v_toPure_3940_, lean_object* v___f_3941_, uint8_t v_____do__lift_3942_){
_start:
{
if (v_____do__lift_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec(v___f_3941_);
v___x_3943_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
lean_ctor_set(v___x_3944_, 1, v_snd_3939_);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___x_3946_ = lean_apply_2(v_toPure_3940_, lean_box(0), v___x_3945_);
return v___x_3946_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_dec(v_toPure_3940_);
lean_dec(v_snd_3939_);
v___x_3947_ = lean_box(0);
v___x_3948_ = lean_apply_1(v___f_3941_, v___x_3947_);
return v___x_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3949_, lean_object* v_toPure_3950_, lean_object* v___f_3951_, lean_object* v_____do__lift_3952_){
_start:
{
uint8_t v_____do__lift_566__boxed_3953_; lean_object* v_res_3954_; 
v_____do__lift_566__boxed_3953_ = lean_unbox(v_____do__lift_3952_);
v_res_3954_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3949_, v_toPure_3950_, v___f_3951_, v_____do__lift_566__boxed_3953_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3955_, lean_object* v_inst_3956_, lean_object* v_toBind_3957_, lean_object* v___f_3958_, lean_object* v_____do__lift_3959_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3960_, 0, v_____do__lift_3959_);
lean_closure_set(v___x_3960_, 1, v_binderType_3955_);
v___x_3961_ = lean_apply_2(v_inst_3956_, lean_box(0), v___x_3960_);
v___x_3962_ = lean_apply_4(v_toBind_3957_, lean_box(0), lean_box(0), v___x_3961_, v___f_3958_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3963_, lean_object* v_toPure_3964_, lean_object* v_levels_x3f_3965_, lean_object* v_inst_3966_, lean_object* v_toBind_3967_, lean_object* v_a_3968_, lean_object* v_x_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_snd_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3991_; 
v_snd_3971_ = lean_ctor_get(v___y_3970_, 1);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___y_3970_);
if (v_isSharedCheck_3991_ == 0)
{
lean_object* v_unused_3992_; 
v_unused_3992_ = lean_ctor_get(v___y_3970_, 0);
lean_dec(v_unused_3992_);
v___x_3973_ = v___y_3970_;
v_isShared_3974_ = v_isSharedCheck_3991_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_snd_3971_);
lean_dec(v___y_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3991_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
if (lean_obj_tag(v_snd_3971_) == 6)
{
lean_object* v_binderType_3975_; lean_object* v_body_3976_; lean_object* v___f_3977_; 
lean_del_object(v___x_3973_);
v_binderType_3975_ = lean_ctor_get(v_snd_3971_, 1);
lean_inc_ref(v_binderType_3975_);
v_body_3976_ = lean_ctor_get(v_snd_3971_, 2);
lean_inc(v_toPure_3964_);
lean_inc(v___x_3963_);
lean_inc_ref(v_a_3968_);
lean_inc_ref(v_body_3976_);
v___f_3977_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3977_, 0, v_body_3976_);
lean_closure_set(v___f_3977_, 1, v_a_3968_);
lean_closure_set(v___f_3977_, 2, v___x_3963_);
lean_closure_set(v___f_3977_, 3, v_toPure_3964_);
if (lean_obj_tag(v_levels_x3f_3965_) == 0)
{
lean_object* v___f_3978_; lean_object* v___f_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_dec(v___x_3963_);
v___f_3978_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3978_, 0, v_snd_3971_);
lean_closure_set(v___f_3978_, 1, v_toPure_3964_);
lean_closure_set(v___f_3978_, 2, v___f_3977_);
lean_inc(v_toBind_3967_);
lean_inc(v_inst_3966_);
v___f_3979_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3979_, 0, v_binderType_3975_);
lean_closure_set(v___f_3979_, 1, v_inst_3966_);
lean_closure_set(v___f_3979_, 2, v_toBind_3967_);
lean_closure_set(v___f_3979_, 3, v___f_3978_);
v___x_3980_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3980_, 0, v_a_3968_);
v___x_3981_ = lean_apply_2(v_inst_3966_, lean_box(0), v___x_3980_);
v___x_3982_ = lean_apply_4(v_toBind_3967_, lean_box(0), lean_box(0), v___x_3981_, v___f_3979_);
return v___x_3982_;
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_inc_ref(v_body_3976_);
lean_dec_ref(v___f_3977_);
lean_dec_ref_known(v_snd_3971_, 3);
lean_dec_ref(v_binderType_3975_);
lean_dec(v_toBind_3967_);
lean_dec(v_inst_3966_);
v___x_3983_ = lean_box(0);
v___x_3984_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3976_, v_a_3968_, v___x_3963_, v_toPure_3964_, v___x_3983_);
lean_dec_ref(v_a_3968_);
lean_dec_ref(v_body_3976_);
return v___x_3984_;
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_dec_ref(v_a_3968_);
lean_dec(v_toBind_3967_);
lean_dec(v_inst_3966_);
lean_dec(v___x_3963_);
v___x_3985_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3985_);
v___x_3987_ = v___x_3973_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_snd_3971_);
v___x_3987_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
v___x_3989_ = lean_apply_2(v_toPure_3964_, lean_box(0), v___x_3988_);
return v___x_3989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3993_, lean_object* v_toPure_3994_, lean_object* v_levels_x3f_3995_, lean_object* v_inst_3996_, lean_object* v_toBind_3997_, lean_object* v_a_3998_, lean_object* v_x_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3993_, v_toPure_3994_, v_levels_x3f_3995_, v_inst_3996_, v_toBind_3997_, v_a_3998_, v_x_3999_, v___y_4000_);
lean_dec(v_levels_x3f_3995_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_4002_, lean_object* v_levels_x3f_4003_, lean_object* v_inst_4004_, lean_object* v_toBind_4005_, lean_object* v_params_4006_, lean_object* v_inst_4007_, lean_object* v___f_4008_, lean_object* v_val_4009_){
_start:
{
lean_object* v___x_4010_; lean_object* v___f_4011_; lean_object* v___x_4012_; size_t v_sz_4013_; size_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4010_ = lean_box(0);
lean_inc(v_toBind_4005_);
v___f_4011_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_4011_, 0, v___x_4010_);
lean_closure_set(v___f_4011_, 1, v_toPure_4002_);
lean_closure_set(v___f_4011_, 2, v_levels_x3f_4003_);
lean_closure_set(v___f_4011_, 3, v_inst_4004_);
lean_closure_set(v___f_4011_, 4, v_toBind_4005_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4010_);
lean_ctor_set(v___x_4012_, 1, v_val_4009_);
v_sz_4013_ = lean_array_size(v_params_4006_);
v___x_4014_ = ((size_t)0ULL);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_4007_, v_params_4006_, v___f_4011_, v_sz_4013_, v___x_4014_, v___x_4012_);
v___x_4016_ = lean_apply_4(v_toBind_4005_, lean_box(0), lean_box(0), v___x_4015_, v___f_4008_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_4017_, lean_object* v_us_4018_, uint8_t v___x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_4017_, v_us_4018_, v___x_4019_, v___y_4022_, v___y_4023_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4026_, lean_object* v_us_4027_, lean_object* v___x_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_677__boxed_4034_; lean_object* v_res_4035_; 
v___x_677__boxed_4034_ = lean_unbox(v___x_4028_);
v_res_4035_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4026_, v_us_4027_, v___x_677__boxed_4034_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v_cinfo_4026_);
return v_res_4035_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4039_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4040_ = lean_unsigned_to_nat(2u);
v___x_4041_ = lean_unsigned_to_nat(202u);
v___x_4042_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4043_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4044_ = l_mkPanicMessageWithDecl(v___x_4043_, v___x_4042_, v___x_4041_, v___x_4040_, v___x_4039_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4045_, lean_object* v___x_4046_, lean_object* v_inst_4047_, lean_object* v_toBind_4048_, lean_object* v___f_4049_, lean_object* v_us_4050_){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4051_ = l_List_lengthTR___redArg(v_us_4050_);
v___x_4052_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4045_);
v___x_4053_ = l_List_lengthTR___redArg(v___x_4052_);
lean_dec(v___x_4052_);
v___x_4054_ = lean_nat_dec_eq(v___x_4051_, v___x_4053_);
lean_dec(v___x_4053_);
lean_dec(v___x_4051_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_dec(v_us_4050_);
lean_dec(v___f_4049_);
lean_dec(v_toBind_4048_);
lean_dec(v_inst_4047_);
lean_dec_ref(v_cinfo_4045_);
v___x_4055_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4056_ = l_panic___redArg(v___x_4046_, v___x_4055_);
return v___x_4056_;
}
else
{
uint8_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___f_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4057_ = 0;
v___x_4058_ = lean_box(v___x_4057_);
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4059_, 0, v_cinfo_4045_);
lean_closure_set(v___f_4059_, 1, v_us_4050_);
lean_closure_set(v___f_4059_, 2, v___x_4058_);
v___x_4060_ = lean_apply_2(v_inst_4047_, lean_box(0), v___f_4059_);
v___x_4061_ = lean_apply_4(v_toBind_4048_, lean_box(0), lean_box(0), v___x_4060_, v___f_4049_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4062_, lean_object* v___x_4063_, lean_object* v_inst_4064_, lean_object* v_toBind_4065_, lean_object* v___f_4066_, lean_object* v_us_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4062_, v___x_4063_, v_inst_4064_, v_toBind_4065_, v___f_4066_, v_us_4067_);
lean_dec(v___x_4063_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4069_, lean_object* v_inst_4070_, lean_object* v_toBind_4071_, lean_object* v___f_4072_, lean_object* v_levels_x3f_4073_, lean_object* v_toPure_4074_, lean_object* v_cinfo_4075_){
_start:
{
lean_object* v___f_4076_; 
lean_inc(v_toBind_4071_);
lean_inc(v_inst_4070_);
lean_inc_ref(v_cinfo_4075_);
v___f_4076_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4076_, 0, v_cinfo_4075_);
lean_closure_set(v___f_4076_, 1, v___x_4069_);
lean_closure_set(v___f_4076_, 2, v_inst_4070_);
lean_closure_set(v___f_4076_, 3, v_toBind_4071_);
lean_closure_set(v___f_4076_, 4, v___f_4072_);
if (lean_obj_tag(v_levels_x3f_4073_) == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
lean_dec(v_toPure_4074_);
v___x_4077_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4077_, 0, v_cinfo_4075_);
v___x_4078_ = lean_apply_2(v_inst_4070_, lean_box(0), v___x_4077_);
v___x_4079_ = lean_apply_4(v_toBind_4071_, lean_box(0), lean_box(0), v___x_4078_, v___f_4076_);
return v___x_4079_;
}
else
{
lean_object* v_val_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v_cinfo_4075_);
lean_dec(v_inst_4070_);
v_val_4080_ = lean_ctor_get(v_levels_x3f_4073_, 0);
lean_inc(v_val_4080_);
lean_dec_ref_known(v_levels_x3f_4073_, 1);
v___x_4081_ = lean_apply_2(v_toPure_4074_, lean_box(0), v_val_4080_);
v___x_4082_ = lean_apply_4(v_toBind_4071_, lean_box(0), lean_box(0), v___x_4081_, v___f_4076_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4083_, lean_object* v_inst_4084_, lean_object* v_inst_4085_, lean_object* v_inst_4086_, lean_object* v_defaultFn_4087_, lean_object* v_levels_x3f_4088_, lean_object* v_params_4089_, lean_object* v_fieldVal_x3f_4090_){
_start:
{
lean_object* v_toApplicative_4091_; lean_object* v_toBind_4092_; lean_object* v_toPure_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___f_4096_; lean_object* v___f_4097_; lean_object* v___x_4098_; lean_object* v___f_4099_; lean_object* v___x_4100_; 
v_toApplicative_4091_ = lean_ctor_get(v_inst_4083_, 0);
v_toBind_4092_ = lean_ctor_get(v_inst_4083_, 1);
lean_inc_n(v_toBind_4092_, 3);
v_toPure_4093_ = lean_ctor_get(v_toApplicative_4091_, 1);
lean_inc_n(v_toPure_4093_, 3);
v___x_4094_ = lean_box(0);
lean_inc_ref_n(v_inst_4083_, 3);
v___x_4095_ = l_Lean_getConstInfo___redArg(v_inst_4083_, v_inst_4084_, v_inst_4085_, v_defaultFn_4087_);
lean_inc_n(v_inst_4086_, 2);
v___f_4096_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4096_, 0, v_inst_4083_);
lean_closure_set(v___f_4096_, 1, v_inst_4086_);
lean_closure_set(v___f_4096_, 2, v_fieldVal_x3f_4090_);
lean_closure_set(v___f_4096_, 3, v_toPure_4093_);
lean_inc(v_levels_x3f_4088_);
v___f_4097_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4097_, 0, v_toPure_4093_);
lean_closure_set(v___f_4097_, 1, v_levels_x3f_4088_);
lean_closure_set(v___f_4097_, 2, v_inst_4086_);
lean_closure_set(v___f_4097_, 3, v_toBind_4092_);
lean_closure_set(v___f_4097_, 4, v_params_4089_);
lean_closure_set(v___f_4097_, 5, v_inst_4083_);
lean_closure_set(v___f_4097_, 6, v___f_4096_);
v___x_4098_ = l_instInhabitedOfMonad___redArg(v_inst_4083_, v___x_4094_);
v___f_4099_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4099_, 0, v___x_4098_);
lean_closure_set(v___f_4099_, 1, v_inst_4086_);
lean_closure_set(v___f_4099_, 2, v_toBind_4092_);
lean_closure_set(v___f_4099_, 3, v___f_4097_);
lean_closure_set(v___f_4099_, 4, v_levels_x3f_4088_);
lean_closure_set(v___f_4099_, 5, v_toPure_4093_);
v___x_4100_ = lean_apply_4(v_toBind_4092_, lean_box(0), lean_box(0), v___x_4095_, v___f_4099_);
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
