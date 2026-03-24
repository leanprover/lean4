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
uint8_t v___x_18671__boxed_466_; lean_object* v_res_467_; 
v___x_18671__boxed_466_ = lean_unbox(v___x_456_);
v_res_467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(v___x_18671__boxed_466_, v_projName_457_, v_n_458_, v_ref_459_, v___f_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
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
lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
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
lean_dec_ref(v___x_748_);
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
lean_dec_ref(v___y_621_);
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
lean_ctor_set(v___x_639_, 0, v___y_632_);
lean_ctor_set(v___x_639_, 1, v___y_635_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*3, v___x_559_);
v___x_640_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = l_Lean_addDecl(v___x_640_, v___y_634_, v___y_636_, v___y_631_);
lean_dec_ref(v___y_636_);
v___y_619_ = v___y_631_;
v___y_620_ = v___y_633_;
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
lean_dec_ref(v___x_674_);
v___x_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_676_, 0, v_a_675_);
v___x_677_ = l_Lean_addDecl(v___x_676_, v___x_649_, v___x_672_, v___y_648_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_dec_ref(v___x_677_);
if (v_instImplicit_554_ == 0)
{
lean_object* v___x_678_; 
lean_inc(v_projName_551_);
v___x_678_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_551_, v___y_645_, v___y_646_, v___x_672_, v___y_648_);
lean_dec_ref(v___x_672_);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_678_;
goto v___jp_618_;
}
else
{
lean_dec_ref(v___x_672_);
v___y_574_ = v___y_648_;
v___y_575_ = v___y_646_;
goto v___jp_573_;
}
}
else
{
lean_dec_ref(v___x_672_);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_677_;
goto v___jp_618_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v___x_672_);
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
lean_inc_ref(v_env_688_);
lean_dec(v___x_687_);
lean_inc_ref(v___x_668_);
lean_inc(v_projName_551_);
v___x_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_689_, 0, v_projName_551_);
lean_ctor_set(v___x_689_, 1, v___x_565_);
lean_ctor_set(v___x_689_, 2, v___x_668_);
lean_inc_ref(v_env_688_);
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
lean_dec_ref(v___x_672_);
v___y_619_ = v___y_648_;
v___y_620_ = v___y_646_;
v___y_621_ = v___x_696_;
goto v___jp_618_;
}
else
{
v___y_631_ = v___y_648_;
v___y_632_ = v___x_689_;
v___y_633_ = v___y_646_;
v___y_634_ = v___x_649_;
v___y_635_ = v___x_670_;
v___y_636_ = v___x_672_;
goto v___jp_630_;
}
}
else
{
lean_dec_ref(v_env_688_);
v___y_631_ = v___y_648_;
v___y_632_ = v___x_689_;
v___y_633_ = v___y_646_;
v___y_634_ = v___x_649_;
v___y_635_ = v___x_670_;
v___y_636_ = v___x_672_;
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
lean_dec_ref(v___x_700_);
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
lean_dec_ref(v___x_700_);
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
lean_dec_ref(v___x_717_);
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
uint8_t v_instImplicit_boxed_780_; uint8_t v___x_18910__boxed_781_; uint8_t v_a_18916__boxed_782_; lean_object* v_res_783_; 
v_instImplicit_boxed_780_ = lean_unbox(v_instImplicit_761_);
v___x_18910__boxed_781_ = lean_unbox(v___x_766_);
v_a_18916__boxed_782_ = lean_unbox(v_a_773_);
v_res_783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(v___x_757_, v_projName_758_, v___x_759_, v_a_760_, v_instImplicit_boxed_780_, v___x_762_, v_params_763_, v_self_764_, v_b_765_, v___x_18910__boxed_781_, v_a_767_, v___x_768_, v_paramInfoOverrides_769_, v_n_770_, v_ref_771_, v___x_772_, v_a_18916__boxed_782_, v_____r_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
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
lean_object* v___x_842_; lean_object* v_env_843_; uint8_t v_isExporting_844_; lean_object* v___x_845_; lean_object* v_env_846_; lean_object* v_nextMacroScope_847_; lean_object* v_ngen_848_; lean_object* v_auxDeclNGen_849_; lean_object* v_traceState_850_; lean_object* v_messages_851_; lean_object* v_infoState_852_; lean_object* v_snapshotTasks_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_907_; 
v___x_842_ = lean_st_ref_get(v___y_840_);
v_env_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_env_843_);
lean_dec(v___x_842_);
v_isExporting_844_ = lean_ctor_get_uint8(v_env_843_, sizeof(void*)*8);
lean_dec_ref(v_env_843_);
v___x_845_ = lean_st_ref_take(v___y_840_);
v_env_846_ = lean_ctor_get(v___x_845_, 0);
v_nextMacroScope_847_ = lean_ctor_get(v___x_845_, 1);
v_ngen_848_ = lean_ctor_get(v___x_845_, 2);
v_auxDeclNGen_849_ = lean_ctor_get(v___x_845_, 3);
v_traceState_850_ = lean_ctor_get(v___x_845_, 4);
v_messages_851_ = lean_ctor_get(v___x_845_, 6);
v_infoState_852_ = lean_ctor_get(v___x_845_, 7);
v_snapshotTasks_853_ = lean_ctor_get(v___x_845_, 8);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_845_, 5);
lean_dec(v_unused_908_);
v___x_855_ = v___x_845_;
v_isShared_856_ = v_isSharedCheck_907_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snapshotTasks_853_);
lean_inc(v_infoState_852_);
lean_inc(v_messages_851_);
lean_inc(v_traceState_850_);
lean_inc(v_auxDeclNGen_849_);
lean_inc(v_ngen_848_);
lean_inc(v_nextMacroScope_847_);
lean_inc(v_env_846_);
lean_dec(v___x_845_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_907_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = l_Lean_Environment_setExporting(v_env_846_, v_isExporting_836_);
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
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_nextMacroScope_847_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_ngen_848_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_auxDeclNGen_849_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_traceState_850_);
lean_ctor_set(v_reuseFailAlloc_906_, 5, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_906_, 6, v_messages_851_);
lean_ctor_set(v_reuseFailAlloc_906_, 7, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_906_, 8, v_snapshotTasks_853_);
v___x_860_ = v_reuseFailAlloc_906_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mctx_863_; lean_object* v_zetaDeltaFVarIds_864_; lean_object* v_postponed_865_; lean_object* v_diag_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_904_; 
v___x_861_ = lean_st_ref_set(v___y_840_, v___x_860_);
v___x_862_ = lean_st_ref_take(v___y_838_);
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
v___x_873_ = lean_st_ref_set(v___y_838_, v___x_872_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
v_r_874_ = lean_apply_5(v_x_835_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, lean_box(0));
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
v___x_881_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_840_, v_isExporting_844_, v___x_858_, v___y_838_, v___x_870_, v___x_880_);
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
lean_dec_ref(v_r_874_);
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_840_, v_isExporting_844_, v___x_858_, v___y_838_, v___x_870_, v___x_893_);
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
lean_inc(v_ref_960_);
lean_inc(v_n_947_);
lean_inc(v_paramInfoOverrides_962_);
lean_inc_ref(v___x_946_);
lean_inc_ref(v_a_945_);
lean_inc_ref(v_b_951_);
lean_inc_ref(v_self_944_);
lean_inc_ref(v_params_943_);
lean_inc(v___x_942_);
lean_inc(v_a_950_);
lean_inc(v___x_940_);
lean_inc(v_projName_961_);
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
lean_inc(v_ref_960_);
lean_inc(v_n_947_);
lean_inc(v_projName_961_);
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
lean_dec_ref(v___x_971_);
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
uint8_t v_instImplicit_boxed_996_; uint8_t v_a_19503__boxed_997_; lean_object* v_res_998_; 
v_instImplicit_boxed_996_ = lean_unbox(v_instImplicit_980_);
v_a_19503__boxed_997_ = lean_unbox(v_a_988_);
v_res_998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_976_, v_projDecls_977_, v___x_978_, v___x_979_, v_instImplicit_boxed_996_, v___x_981_, v_params_982_, v_self_983_, v_a_984_, v___x_985_, v_n_986_, v___x_987_, v_a_19503__boxed_997_, v_a_989_, v_b_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
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
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_b_1003_);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1010_ = lean_array_uget_borrowed(v_as_1000_, v_i_1002_);
v___x_1011_ = l_Lean_Expr_fvarId_x21(v_a_1010_);
lean_inc_ref(v___y_1004_);
lean_inc(v___x_1011_);
v___x_1012_ = l_Lean_FVarId_getDecl___redArg(v___x_1011_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v_a_1015_; uint8_t v___y_1020_; uint8_t v___x_1023_; uint8_t v___x_1024_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1023_ = l_Lean_LocalDecl_binderInfo(v_a_1013_);
v___x_1024_ = l_Lean_BinderInfo_isInstImplicit(v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1026_ = l_Lean_LocalDecl_type(v_a_1013_);
lean_dec(v_a_1013_);
v___x_1027_ = lean_is_out_param(v___x_1026_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = 0;
v___x_1029_ = l_Lean_LocalContext_setBinderInfo(v_b_1003_, v___x_1011_, v___x_1028_);
v_a_1015_ = v___x_1029_;
goto v___jp_1014_;
}
else
{
goto v___jp_1025_;
}
}
else
{
lean_dec(v_a_1013_);
goto v___jp_1025_;
}
v___jp_1014_:
{
size_t v___x_1016_; size_t v___x_1017_; 
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_add(v_i_1002_, v___x_1016_);
v_i_1002_ = v___x_1017_;
v_b_1003_ = v_a_1015_;
goto _start;
}
v___jp_1019_:
{
if (v___y_1020_ == 0)
{
lean_dec(v___x_1011_);
v_a_1015_ = v_b_1003_;
goto v___jp_1014_;
}
else
{
uint8_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = 1;
v___x_1022_ = l_Lean_LocalContext_setBinderInfo(v_b_1003_, v___x_1011_, v___x_1021_);
v_a_1015_ = v___x_1022_;
goto v___jp_1014_;
}
}
v___jp_1025_:
{
if (v___x_1024_ == 0)
{
v___y_1020_ = v___x_1024_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v_instImplicit_999_;
goto v___jp_1019_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___x_1011_);
lean_dec_ref(v_b_1003_);
v_a_1030_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1012_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1012_);
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
lean_dec_ref(v___x_1071_);
v___x_1073_ = lean_array_get_size(v_projDecls_1053_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_1073_, v_projDecls_1053_, v_toConstantVal_1054_, v_numParams_1055_, v_instImplicit_1052_, v___x_1056_, v_params_1051_, v_self_1061_, v_a_1072_, v___x_1068_, v_n_1057_, v_levelParams_1058_, v_a_1059_, v___x_1074_, v_ctorType_1060_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec_ref(v___y_1062_);
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
lean_dec_ref(v___y_1062_);
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
uint8_t v_instImplicit_boxed_1117_; uint8_t v_a_19645__boxed_1118_; lean_object* v_res_1119_; 
v_instImplicit_boxed_1117_ = lean_unbox(v_instImplicit_1102_);
v_a_19645__boxed_1118_ = lean_unbox(v_a_1109_);
v_res_1119_ = l_Lean_Meta_mkProjections___lam__0(v_params_1101_, v_instImplicit_boxed_1117_, v_projDecls_1103_, v_toConstantVal_1104_, v_numParams_1105_, v___x_1106_, v_n_1107_, v_levelParams_1108_, v_a_19645__boxed_1118_, v_ctorType_1110_, v_self_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
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
v___x_1154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1152_, v___y_1151_, v___y_1150_, v___y_1149_, v___x_1153_, v___y_1148_, v___y_1146_, v___y_1145_, v___y_1147_);
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
v___y_1145_ = v___y_1141_;
v___y_1146_ = v___y_1140_;
v___y_1147_ = v___y_1142_;
v___y_1148_ = v___y_1139_;
v___y_1149_ = v___f_1157_;
v___y_1150_ = v___x_1160_;
v___y_1151_ = v___x_1161_;
goto v___jp_1144_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = 3;
v___y_1145_ = v___y_1141_;
v___y_1146_ = v___y_1140_;
v___y_1147_ = v___y_1142_;
v___y_1148_ = v___y_1139_;
v___y_1149_ = v___f_1157_;
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
uint8_t v_instImplicit_boxed_1186_; uint8_t v_a_19749__boxed_1187_; lean_object* v_res_1188_; 
v_instImplicit_boxed_1186_ = lean_unbox(v_instImplicit_1171_);
v_a_19749__boxed_1187_ = lean_unbox(v_a_1178_);
v_res_1188_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1186_, v_projDecls_1172_, v_toConstantVal_1173_, v_numParams_1174_, v___x_1175_, v_n_1176_, v_levelParams_1177_, v_a_19749__boxed_1187_, v_params_1179_, v_ctorType_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
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
v___x_1203_ = l_instMonadEIO(lean_box(0));
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
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_14615__overap_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = l_instInhabitedOfMonad___redArg(v___x_1262_, v___x_1263_);
v___x_14615__overap_1265_ = lean_panic_fn(v___x_1264_, v_msg_1208_);
lean_inc(v___y_1212_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
v___x_1266_ = lean_apply_5(v___x_14615__overap_1265_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, lean_box(0));
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
lean_dec_ref(v___x_1315_);
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
lean_dec_ref(v_a_1329_);
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
lean_dec_ref(v___x_1402_);
v___x_1444_ = l_Lean_InductiveVal_numCtors(v_a_1403_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_a_1403_);
lean_dec_ref(v_projDecls_1396_);
lean_dec(v___x_1394_);
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
lean_dec_ref(v___x_1413_);
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
lean_dec_ref(v___x_1417_);
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
lean_dec(v___x_1394_);
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
return v_res_1471_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = lean_unsigned_to_nat(32u);
v___x_1476_ = lean_mk_empty_array_with_capacity(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
size_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = ((size_t)5ULL);
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_unsigned_to_nat(32u);
v___x_1481_ = lean_mk_empty_array_with_capacity(v___x_1480_);
v___x_1482_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1483_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
lean_ctor_set(v___x_1483_, 2, v___x_1479_);
lean_ctor_set(v___x_1483_, 3, v___x_1479_);
lean_ctor_set_usize(v___x_1483_, 4, v___x_1478_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__4(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1484_ = lean_box(1);
v___x_1485_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1486_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
lean_ctor_set(v___x_1487_, 2, v___x_1484_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1490_, lean_object* v_projDecls_1491_, uint8_t v_instImplicit_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_box(v_instImplicit_1492_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1500_, 0, v_n_1490_);
lean_closure_set(v___f_1500_, 1, v___x_1498_);
lean_closure_set(v___f_1500_, 2, v___x_1499_);
lean_closure_set(v___f_1500_, 3, v_projDecls_1491_);
v___x_1501_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__4, &l_Lean_Meta_mkProjections___closed__4_once, _init_l_Lean_Meta_mkProjections___closed__4);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__5));
v___x_1503_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(v___x_1501_, v___x_1502_, v___f_1500_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1504_, lean_object* v_projDecls_1505_, lean_object* v_instImplicit_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
uint8_t v_instImplicit_boxed_1512_; lean_object* v_res_1513_; 
v_instImplicit_boxed_1512_ = lean_unbox(v_instImplicit_1506_);
v_res_1513_ = l_Lean_Meta_mkProjections(v_n_1504_, v_projDecls_1505_, v_instImplicit_boxed_1512_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1514_, v_as_1515_, v_sz_1516_, v_i_1517_, v_b_1518_, v___y_1519_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1525_, lean_object* v_as_1526_, lean_object* v_sz_1527_, lean_object* v_i_1528_, lean_object* v_b_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_instImplicit_boxed_1535_; size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_instImplicit_boxed_1535_ = lean_unbox(v_instImplicit_1525_);
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1527_);
lean_dec(v_sz_1527_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1535_, v_as_1526_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_as_1526_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(lean_object* v_declName_1539_, uint8_t v_s_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_1539_, v_s_1540_, v___y_1542_, v___y_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(lean_object* v_declName_1547_, lean_object* v_s_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_s_boxed_1554_; lean_object* v_res_1555_; 
v_s_boxed_1554_ = lean_unbox(v_s_1548_);
v_res_1555_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_1547_, v_s_boxed_1554_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_00_u03b1_1556_, lean_object* v_ref_1557_, lean_object* v_msg_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_1557_, v_msg_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_ref_1566_, lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(v_00_u03b1_1565_, v_ref_1566_, v_msg_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v_ref_1566_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(lean_object* v_00_u03b1_1574_, lean_object* v_x_1575_, uint8_t v_isExporting_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_1575_, v_isExporting_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_x_1584_, lean_object* v_isExporting_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_isExporting_boxed_1591_; lean_object* v_res_1592_; 
v_isExporting_boxed_1591_ = lean_unbox(v_isExporting_1585_);
v_res_1592_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_1583_, v_x_1584_, v_isExporting_boxed_1591_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1593_, lean_object* v_x_1594_, uint8_t v_when_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(v_x_1594_, v_when_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1602_, lean_object* v_x_1603_, lean_object* v_when_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v_when_boxed_1610_; lean_object* v_res_1611_; 
v_when_boxed_1610_ = lean_unbox(v_when_1604_);
v_res_1611_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1602_, v_x_1603_, v_when_boxed_1610_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_upperBound_1612_, lean_object* v_projDecls_1613_, lean_object* v___x_1614_, lean_object* v___x_1615_, uint8_t v_instImplicit_1616_, lean_object* v___x_1617_, lean_object* v_params_1618_, lean_object* v_self_1619_, lean_object* v_a_1620_, lean_object* v___x_1621_, lean_object* v_n_1622_, lean_object* v___x_1623_, uint8_t v_a_1624_, lean_object* v_inst_1625_, lean_object* v_R_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_c_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v_upperBound_1612_, v_projDecls_1613_, v___x_1614_, v___x_1615_, v_instImplicit_1616_, v___x_1617_, v_params_1618_, v_self_1619_, v_a_1620_, v___x_1621_, v_n_1622_, v___x_1623_, v_a_1624_, v_a_1627_, v_b_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_1636_ = _args[0];
lean_object* v_projDecls_1637_ = _args[1];
lean_object* v___x_1638_ = _args[2];
lean_object* v___x_1639_ = _args[3];
lean_object* v_instImplicit_1640_ = _args[4];
lean_object* v___x_1641_ = _args[5];
lean_object* v_params_1642_ = _args[6];
lean_object* v_self_1643_ = _args[7];
lean_object* v_a_1644_ = _args[8];
lean_object* v___x_1645_ = _args[9];
lean_object* v_n_1646_ = _args[10];
lean_object* v___x_1647_ = _args[11];
lean_object* v_a_1648_ = _args[12];
lean_object* v_inst_1649_ = _args[13];
lean_object* v_R_1650_ = _args[14];
lean_object* v_a_1651_ = _args[15];
lean_object* v_b_1652_ = _args[16];
lean_object* v_c_1653_ = _args[17];
lean_object* v___y_1654_ = _args[18];
lean_object* v___y_1655_ = _args[19];
lean_object* v___y_1656_ = _args[20];
lean_object* v___y_1657_ = _args[21];
lean_object* v___y_1658_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1659_; uint8_t v_a_20502__boxed_1660_; lean_object* v_res_1661_; 
v_instImplicit_boxed_1659_ = lean_unbox(v_instImplicit_1640_);
v_a_20502__boxed_1660_ = lean_unbox(v_a_1648_);
v_res_1661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(v_upperBound_1636_, v_projDecls_1637_, v___x_1638_, v___x_1639_, v_instImplicit_boxed_1659_, v___x_1641_, v_params_1642_, v_self_1643_, v_a_1644_, v___x_1645_, v_n_1646_, v___x_1647_, v_a_20502__boxed_1660_, v_inst_1649_, v_R_1650_, v_a_1651_, v_b_1652_, v_c_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec_ref(v_projDecls_1637_);
lean_dec(v_upperBound_1636_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1662_, uint8_t v_allowLevelAssignments_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1663_, v_k_1662_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
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
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1669_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1669_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1686_, lean_object* v_allowLevelAssignments_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1693_; lean_object* v_res_1694_; 
v_allowLevelAssignments_boxed_1693_ = lean_unbox(v_allowLevelAssignments_1687_);
v_res_1694_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1686_, v_allowLevelAssignments_boxed_1693_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1695_, lean_object* v_k_1696_, uint8_t v_allowLevelAssignments_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1696_, v_allowLevelAssignments_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_k_1705_, lean_object* v_allowLevelAssignments_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1712_; lean_object* v_res_1713_; 
v_allowLevelAssignments_boxed_1712_ = lean_unbox(v_allowLevelAssignments_1706_);
v_res_1713_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1704_, v_k_1705_, v_allowLevelAssignments_boxed_1712_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1714_, size_t v_sz_1715_, size_t v_i_1716_, lean_object* v_b_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1716_, v_sz_1715_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_b_1717_);
return v___x_1724_;
}
else
{
lean_object* v_snd_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1780_; 
v_snd_1725_ = lean_ctor_get(v_b_1717_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_b_1717_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_b_1717_, 0);
lean_dec(v_unused_1781_);
v___x_1727_ = v_b_1717_;
v_isShared_1728_ = v_isSharedCheck_1780_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1725_);
lean_dec(v_b_1717_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1780_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_array_1729_; lean_object* v_start_1730_; lean_object* v_stop_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_array_1729_ = lean_ctor_get(v_snd_1725_, 0);
v_start_1730_ = lean_ctor_get(v_snd_1725_, 1);
v_stop_1731_ = lean_ctor_get(v_snd_1725_, 2);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_nat_dec_lt(v_start_1730_, v_stop_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1735_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1732_);
v___x_1735_ = v___x_1727_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_snd_1725_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
else
{
lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1776_; 
lean_inc(v_stop_1731_);
lean_inc(v_start_1730_);
lean_inc_ref(v_array_1729_);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_snd_1725_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; 
v_unused_1777_ = lean_ctor_get(v_snd_1725_, 2);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_snd_1725_, 1);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_snd_1725_, 0);
lean_dec(v_unused_1779_);
v___x_1739_ = v_snd_1725_;
v_isShared_1740_ = v_isSharedCheck_1776_;
goto v_resetjp_1738_;
}
else
{
lean_dec(v_snd_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1776_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_a_1741_ = lean_array_uget_borrowed(v_as_1714_, v_i_1716_);
v___x_1742_ = lean_array_fget_borrowed(v_array_1729_, v_start_1730_);
lean_inc(v___x_1742_);
lean_inc(v_a_1741_);
v___x_1743_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1741_, v___x_1742_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1767_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1767_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1767_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v_start_1730_, v___x_1748_);
lean_dec(v_start_1730_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1749_);
v___x_1751_ = v___x_1739_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_array_1729_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_stop_1731_);
v___x_1751_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_unbox(v_a_1744_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1744_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1751_);
lean_ctor_set(v___x_1727_, 0, v___x_1753_);
v___x_1755_ = v___x_1727_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1751_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1755_);
v___x_1757_ = v___x_1746_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v___x_1761_; 
lean_del_object(v___x_1746_);
lean_dec(v_a_1744_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1751_);
lean_ctor_set(v___x_1727_, 0, v___x_1732_);
v___x_1761_ = v___x_1727_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1751_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
size_t v___x_1762_; size_t v___x_1763_; 
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1716_, v___x_1762_);
v_i_1716_ = v___x_1763_;
v_b_1717_ = v___x_1761_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_del_object(v___x_1739_);
lean_dec(v_stop_1731_);
lean_dec(v_start_1730_);
lean_dec_ref(v_array_1729_);
lean_del_object(v___x_1727_);
v_a_1768_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1743_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1743_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1782_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_as_1782_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1794_, lean_object* v_params2_1795_, lean_object* v___x_1796_, lean_object* v_params1_1797_, uint8_t v___x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
if (v___x_1794_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v___x_1796_);
lean_dec_ref(v_params2_1795_);
v___x_1804_ = lean_box(v___x_1794_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = l_Array_toSubarray___redArg(v_params2_1795_, v___x_1806_, v___x_1796_);
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1807_);
v_sz_1810_ = lean_array_size(v_params1_1797_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1797_, v_sz_1810_, v___x_1811_, v___x_1809_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1826_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1826_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_fst_1817_; 
v_fst_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_fst_1817_);
lean_dec(v_a_1813_);
if (lean_obj_tag(v_fst_1817_) == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_box(v___x_1798_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
else
{
lean_object* v_val_1822_; lean_object* v___x_1824_; 
v_val_1822_ = lean_ctor_get(v_fst_1817_, 0);
lean_inc(v_val_1822_);
lean_dec_ref(v_fst_1817_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_val_1822_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_val_1822_);
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
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_a_1827_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1812_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1812_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1835_, lean_object* v_params2_1836_, lean_object* v___x_1837_, lean_object* v_params1_1838_, lean_object* v___x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_2097__boxed_1845_; uint8_t v___x_2099__boxed_1846_; lean_object* v_res_1847_; 
v___x_2097__boxed_1845_ = lean_unbox(v___x_1835_);
v___x_2099__boxed_1846_ = lean_unbox(v___x_1839_);
v_res_1847_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2097__boxed_1845_, v_params2_1836_, v___x_1837_, v_params1_1838_, v___x_2099__boxed_1846_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v_params1_1838_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1848_, lean_object* v_params2_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___y_1861_; uint8_t v___x_1862_; lean_object* v___x_1863_; 
v___x_1855_ = lean_array_get_size(v_params1_1848_);
v___x_1856_ = lean_array_get_size(v_params2_1849_);
v___x_1857_ = lean_nat_dec_eq(v___x_1855_, v___x_1856_);
v___x_1858_ = 1;
v___x_1859_ = lean_box(v___x_1857_);
v___x_1860_ = lean_box(v___x_1858_);
v___y_1861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1861_, 0, v___x_1859_);
lean_closure_set(v___y_1861_, 1, v_params2_1849_);
lean_closure_set(v___y_1861_, 2, v___x_1856_);
lean_closure_set(v___y_1861_, 3, v_params1_1848_);
lean_closure_set(v___y_1861_, 4, v___x_1860_);
v___x_1862_ = 0;
v___x_1863_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1861_, v___x_1862_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1864_, lean_object* v_params2_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1864_, v_params2_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v_env_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = lean_st_ref_get(v___y_1873_);
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc_ref(v_env_1876_);
lean_dec(v___x_1875_);
v___x_1877_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1876_, v_declName_1872_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1879_, v___y_1880_);
lean_dec(v___y_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1883_, v___y_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1897_; lean_object* v_dummy_1898_; 
v___x_1897_ = lean_box(0);
v_dummy_1898_ = l_Lean_Expr_sort___override(v___x_1897_);
return v_dummy_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1899_, lean_object* v_induct_1900_, lean_object* v_params_1901_, lean_object* v_idx_1902_, lean_object* v_e_1903_, lean_object* v_x_x3f_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
if (lean_obj_tag(v_e_1903_) == 11)
{
lean_object* v_typeName_1916_; lean_object* v_idx_1917_; lean_object* v_struct_1918_; uint8_t v___y_1966_; uint8_t v___x_1969_; 
v_typeName_1916_ = lean_ctor_get(v_e_1903_, 0);
v_idx_1917_ = lean_ctor_get(v_e_1903_, 1);
v_struct_1918_ = lean_ctor_get(v_e_1903_, 2);
lean_inc_ref(v_struct_1918_);
v___x_1969_ = lean_nat_dec_eq(v_idx_1917_, v_idx_1902_);
if (v___x_1969_ == 0)
{
v___y_1966_ = v___x_1969_;
goto v___jp_1965_;
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_name_eq(v_induct_1900_, v_typeName_1916_);
v___y_1966_ = v___x_1970_;
goto v___jp_1965_;
}
v___jp_1919_:
{
lean_object* v___x_1920_; 
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
v___x_1920_ = lean_infer_type(v_e_1903_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
v___x_1922_ = lean_whnf(v_a_1921_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v_dummy_1924_; lean_object* v_nargs_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1922_);
v_dummy_1924_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1925_ = l_Lean_Expr_getAppNumArgs(v_a_1923_);
lean_inc(v_nargs_1925_);
v___x_1926_ = lean_mk_array(v_nargs_1925_, v_dummy_1924_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_sub(v_nargs_1925_, v___x_1927_);
lean_dec(v_nargs_1925_);
v___x_1929_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1923_, v___x_1926_, v___x_1928_);
v___x_1930_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1901_, v___x_1929_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1940_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1940_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_unbox(v_a_1931_);
lean_dec(v_a_1931_);
if (v___x_1935_ == 0)
{
lean_del_object(v___x_1933_);
lean_dec_ref(v_struct_1918_);
goto v___jp_1910_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_struct_1918_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1936_);
v___x_1938_ = v___x_1933_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
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
lean_dec_ref(v_struct_1918_);
v_a_1941_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1930_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1930_);
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
lean_dec_ref(v_struct_1918_);
lean_dec_ref(v_params_1901_);
v_a_1949_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1922_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1922_);
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
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_struct_1918_);
lean_dec_ref(v_params_1901_);
v_a_1957_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1920_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1920_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
v___jp_1965_:
{
if (v___y_1966_ == 0)
{
lean_dec_ref(v_struct_1918_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1910_;
}
else
{
if (lean_obj_tag(v_x_x3f_1904_) == 0)
{
goto v___jp_1919_;
}
else
{
lean_object* v_val_1967_; uint8_t v___x_1968_; 
v_val_1967_ = lean_ctor_get(v_x_x3f_1904_, 0);
v___x_1968_ = lean_expr_eqv(v_val_1967_, v_struct_1918_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v_struct_1918_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1910_;
}
else
{
goto v___jp_1919_;
}
}
}
}
}
else
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Expr_getAppFn(v_e_1903_);
if (lean_obj_tag(v___x_1971_) == 4)
{
lean_object* v_declName_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2023_; 
v_declName_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_declName_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1972_, v_a_1908_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2023_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2023_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___y_1979_; lean_object* v___y_1980_; 
if (lean_obj_tag(v_a_1974_) == 1)
{
lean_object* v_val_2008_; lean_object* v_ctorName_2009_; lean_object* v_numParams_2010_; lean_object* v_i_2011_; uint8_t v___y_2013_; uint8_t v___x_2021_; 
v_val_2008_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_val_2008_);
lean_dec_ref(v_a_1974_);
v_ctorName_2009_ = lean_ctor_get(v_val_2008_, 0);
lean_inc(v_ctorName_2009_);
v_numParams_2010_ = lean_ctor_get(v_val_2008_, 1);
lean_inc(v_numParams_2010_);
v_i_2011_ = lean_ctor_get(v_val_2008_, 2);
lean_inc(v_i_2011_);
lean_dec(v_val_2008_);
v___x_2021_ = lean_name_eq(v_ctorName_2009_, v_ctor_1899_);
lean_dec(v_ctorName_2009_);
if (v___x_2021_ == 0)
{
lean_dec(v_i_2011_);
v___y_2013_ = v___x_2021_;
goto v___jp_2012_;
}
else
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_nat_dec_eq(v_i_2011_, v_idx_1902_);
lean_dec(v_i_2011_);
v___y_2013_ = v___x_2022_;
goto v___jp_2012_;
}
v___jp_2012_:
{
if (v___y_2013_ == 0)
{
lean_dec(v_numParams_2010_);
lean_del_object(v___x_1976_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2014_ = l_Lean_Expr_getAppNumArgs(v_e_1903_);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_numParams_2010_, v___x_2015_);
lean_dec(v_numParams_2010_);
v___x_2017_ = lean_nat_dec_eq(v___x_2014_, v___x_2016_);
lean_dec(v___x_2016_);
lean_dec(v___x_2014_);
if (v___x_2017_ == 0)
{
lean_del_object(v___x_1976_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_Expr_appArg_x21(v_e_1903_);
if (lean_obj_tag(v_x_x3f_1904_) == 0)
{
v___y_1979_ = v___x_2018_;
v___y_1980_ = v___x_2015_;
goto v___jp_1978_;
}
else
{
lean_object* v_val_2019_; uint8_t v___x_2020_; 
v_val_2019_ = lean_ctor_get(v_x_x3f_1904_, 0);
v___x_2020_ = lean_expr_eqv(v_val_2019_, v___x_2018_);
if (v___x_2020_ == 0)
{
lean_dec_ref(v___x_2018_);
lean_del_object(v___x_1976_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1913_;
}
else
{
v___y_1979_ = v___x_2018_;
v___y_1980_ = v___x_2015_;
goto v___jp_1978_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1976_);
lean_dec(v_a_1974_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1913_;
}
v___jp_1978_:
{
lean_object* v___x_1981_; lean_object* v_dummy_1982_; lean_object* v_nargs_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1981_ = l_Lean_Expr_appFn_x21(v_e_1903_);
lean_dec_ref(v_e_1903_);
v_dummy_1982_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1983_ = l_Lean_Expr_getAppNumArgs(v___x_1981_);
lean_inc(v_nargs_1983_);
v___x_1984_ = lean_mk_array(v_nargs_1983_, v_dummy_1982_);
v___x_1985_ = lean_nat_sub(v_nargs_1983_, v___y_1980_);
lean_dec(v_nargs_1983_);
v___x_1986_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1981_, v___x_1984_, v___x_1985_);
v___x_1987_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1901_, v___x_1986_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1999_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1999_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1999_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
if (v___x_1992_ == 0)
{
lean_del_object(v___x_1990_);
lean_dec_ref(v___y_1979_);
lean_del_object(v___x_1976_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_1994_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 1);
lean_ctor_set(v___x_1976_, 0, v___y_1979_);
v___x_1994_ = v___x_1976_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___y_1979_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1994_);
v___x_1996_ = v___x_1990_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v___y_1979_);
lean_del_object(v___x_1976_);
v_a_2000_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1987_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1987_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_e_1903_);
lean_dec_ref(v_params_1901_);
goto v___jp_1913_;
}
}
v___jp_1910_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
v___jp_1913_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2024_, lean_object* v_induct_2025_, lean_object* v_params_2026_, lean_object* v_idx_2027_, lean_object* v_e_2028_, lean_object* v_x_x3f_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2024_, v_induct_2025_, v_params_2026_, v_idx_2027_, v_e_2028_, v_x_x3f_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_x_x3f_2029_);
lean_dec(v_idx_2027_);
lean_dec(v_induct_2025_);
lean_dec(v_ctor_2024_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_env_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2042_ = lean_st_ref_get(v___y_2040_);
v_env_2046_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2042_);
v___x_2047_ = 0;
v___x_2048_ = l_Lean_Environment_findAsync_x3f(v_env_2046_, v_constName_2036_, v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 1)
{
lean_object* v_val_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2068_; 
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2068_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_val_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2068_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
uint8_t v_kind_2053_; 
v_kind_2053_ = lean_ctor_get_uint8(v_val_2049_, sizeof(void*)*3);
if (v_kind_2053_ == 6)
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2049_);
if (lean_obj_tag(v___x_2054_) == 6)
{
lean_object* v_val_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2065_; 
v_val_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2065_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_val_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2065_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v_val_2055_);
v___x_2060_ = v___x_2051_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_val_2055_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2060_);
v___x_2062_ = v___x_2057_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
lean_dec_ref(v___x_2054_);
lean_del_object(v___x_2051_);
v___x_2066_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2067_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2066_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v___x_2067_;
}
}
else
{
lean_del_object(v___x_2051_);
lean_dec(v_val_2049_);
goto v___jp_2043_;
}
}
}
else
{
lean_dec(v___x_2048_);
goto v___jp_2043_;
}
v___jp_2043_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2084_, lean_object* v___x_2085_, lean_object* v___x_2086_, lean_object* v_declName_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v_a_2090_, lean_object* v_val_2091_, lean_object* v_a_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_nat_dec_lt(v_a_2092_, v_upperBound_2084_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec(v_a_2092_);
lean_dec_ref(v___x_2089_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_b_2093_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref(v_b_2093_);
v___x_2101_ = l_Lean_instInhabitedExpr;
v___x_2102_ = lean_nat_add(v___x_2085_, v_a_2092_);
v___x_2103_ = lean_array_get_borrowed(v___x_2101_, v___x_2086_, v___x_2102_);
lean_dec(v___x_2102_);
lean_inc(v___x_2103_);
lean_inc_ref(v___x_2089_);
v___x_2104_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2087_, v___x_2088_, v___x_2089_, v_a_2092_, v___x_2103_, v_a_2090_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2123_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2123_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2123_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
if (lean_obj_tag(v_a_2105_) == 1)
{
lean_object* v_val_2109_; uint8_t v___x_2110_; 
v_val_2109_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2109_);
lean_dec_ref(v_a_2105_);
v___x_2110_ = lean_expr_eqv(v_val_2109_, v_val_2091_);
lean_dec(v_val_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v_a_2092_);
lean_dec_ref(v___x_2089_);
v___x_2111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2111_);
v___x_2113_ = v___x_2107_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_del_object(v___x_2107_);
v___x_2115_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2116_ = lean_unsigned_to_nat(1u);
v___x_2117_ = lean_nat_add(v_a_2092_, v___x_2116_);
lean_dec(v_a_2092_);
v_a_2092_ = v___x_2117_;
v_b_2093_ = v___x_2115_;
goto _start;
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec(v_a_2105_);
lean_dec(v_a_2092_);
lean_dec_ref(v___x_2089_);
v___x_2119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1));
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2119_);
v___x_2121_ = v___x_2107_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_a_2092_);
lean_dec_ref(v___x_2089_);
v_a_2124_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2104_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2104_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2132_, lean_object* v___x_2133_, lean_object* v___x_2134_, lean_object* v_declName_2135_, lean_object* v___x_2136_, lean_object* v___x_2137_, lean_object* v_a_2138_, lean_object* v_val_2139_, lean_object* v_a_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2132_, v___x_2133_, v___x_2134_, v_declName_2135_, v___x_2136_, v___x_2137_, v_a_2138_, v_val_2139_, v_a_2140_, v_b_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v_val_2139_);
lean_dec(v_a_2138_);
lean_dec(v___x_2136_);
lean_dec(v_declName_2135_);
lean_dec_ref(v___x_2134_);
lean_dec(v___x_2133_);
lean_dec(v_upperBound_2132_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2148_, lean_object* v_p_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_Expr_getAppFn(v_e_2148_);
if (lean_obj_tag(v___x_2155_) == 4)
{
lean_object* v_declName_2156_; lean_object* v___x_2157_; 
v_declName_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_declName_2156_);
lean_dec_ref(v___x_2155_);
lean_inc(v_declName_2156_);
v___x_2157_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2156_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2230_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2230_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2230_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v_val_2162_; lean_object* v_induct_2163_; lean_object* v_numParams_2164_; lean_object* v_numFields_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v_val_2162_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_val_2162_);
lean_dec_ref(v_a_2158_);
v_induct_2163_ = lean_ctor_get(v_val_2162_, 1);
lean_inc(v_induct_2163_);
v_numParams_2164_ = lean_ctor_get(v_val_2162_, 3);
lean_inc(v_numParams_2164_);
v_numFields_2165_ = lean_ctor_get(v_val_2162_, 4);
lean_inc(v_numFields_2165_);
lean_dec(v_val_2162_);
lean_inc(v_induct_2163_);
v___x_2166_ = lean_apply_1(v_p_2149_, v_induct_2163_);
v___x_2167_ = lean_unbox(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2156_);
lean_dec_ref(v_e_2148_);
v___x_2168_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2168_);
v___x_2170_ = v___x_2160_;
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
lean_object* v___x_2172_; uint8_t v___y_2174_; uint8_t v___x_2222_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_nat_dec_lt(v___x_2172_, v_numFields_2165_);
if (v___x_2222_ == 0)
{
v___y_2174_ = v___x_2222_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2223_ = l_Lean_Expr_getAppNumArgs(v_e_2148_);
v___x_2224_ = lean_nat_add(v_numParams_2164_, v_numFields_2165_);
v___x_2225_ = lean_nat_dec_eq(v___x_2223_, v___x_2224_);
lean_dec(v___x_2224_);
lean_dec(v___x_2223_);
v___y_2174_ = v___x_2225_;
goto v___jp_2173_;
}
v___jp_2173_:
{
if (v___y_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2156_);
lean_dec_ref(v_e_2148_);
v___x_2175_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2175_);
v___x_2177_ = v___x_2160_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
else
{
lean_object* v_dummy_2179_; lean_object* v_nargs_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_del_object(v___x_2160_);
v_dummy_2179_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2180_ = l_Lean_Expr_getAppNumArgs(v_e_2148_);
lean_inc(v_nargs_2180_);
v___x_2181_ = lean_mk_array(v_nargs_2180_, v_dummy_2179_);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_sub(v_nargs_2180_, v___x_2182_);
lean_dec(v_nargs_2180_);
v___x_2184_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2148_, v___x_2181_, v___x_2183_);
lean_inc(v_numParams_2164_);
v___x_2185_ = l_Array_extract___redArg(v___x_2184_, v___x_2172_, v_numParams_2164_);
v___x_2186_ = l_Lean_instInhabitedExpr;
v___x_2187_ = lean_array_get(v___x_2186_, v___x_2184_, v_numParams_2164_);
v___x_2188_ = lean_box(0);
lean_inc_ref(v___x_2185_);
v___x_2189_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2156_, v_induct_2163_, v___x_2185_, v___x_2172_, v___x_2187_, v___x_2188_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2221_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2221_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2221_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
if (lean_obj_tag(v_a_2190_) == 1)
{
lean_object* v_val_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_del_object(v___x_2192_);
v_val_2194_ = lean_ctor_get(v_a_2190_, 0);
v___x_2195_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
v___x_2196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2165_, v_numParams_2164_, v___x_2184_, v_declName_2156_, v_induct_2163_, v___x_2185_, v_a_2190_, v_val_2194_, v___x_2182_, v___x_2195_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2156_);
lean_dec_ref(v___x_2184_);
lean_dec(v_numParams_2164_);
lean_dec(v_numFields_2165_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2209_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_fst_2201_; 
v_fst_2201_ = lean_ctor_get(v_a_2197_, 0);
lean_inc(v_fst_2201_);
lean_dec(v_a_2197_);
if (lean_obj_tag(v_fst_2201_) == 0)
{
lean_object* v___x_2203_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_a_2190_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2190_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2207_; 
lean_dec_ref(v_a_2190_);
v_val_2205_ = lean_ctor_get(v_fst_2201_, 0);
lean_inc(v_val_2205_);
lean_dec_ref(v_fst_2201_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v_val_2205_);
v___x_2207_ = v___x_2199_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_val_2205_);
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
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_a_2190_);
v_a_2210_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2196_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2196_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
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
lean_object* v___x_2219_; 
lean_dec(v_a_2190_);
lean_dec_ref(v___x_2185_);
lean_dec_ref(v___x_2184_);
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2156_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2188_);
v___x_2219_ = v___x_2192_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2188_);
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
lean_dec_ref(v___x_2185_);
lean_dec_ref(v___x_2184_);
lean_dec(v_numFields_2165_);
lean_dec(v_numParams_2164_);
lean_dec(v_induct_2163_);
lean_dec(v_declName_2156_);
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_dec(v_a_2158_);
lean_dec(v_declName_2156_);
lean_dec_ref(v_p_2149_);
lean_dec_ref(v_e_2148_);
v___x_2226_ = lean_box(0);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2226_);
v___x_2228_ = v___x_2160_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_declName_2156_);
lean_dec_ref(v_p_2149_);
lean_dec_ref(v_e_2148_);
v_a_2231_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2157_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2157_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
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
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v___x_2155_);
lean_dec_ref(v_p_2149_);
lean_dec_ref(v_e_2148_);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2241_, lean_object* v_p_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Meta_etaStruct_x3f(v_e_2241_, v_p_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2249_, lean_object* v___x_2250_, lean_object* v___x_2251_, lean_object* v_declName_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v_a_2255_, lean_object* v_val_2256_, lean_object* v_inst_2257_, lean_object* v_R_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_, lean_object* v_c_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2249_, v___x_2250_, v___x_2251_, v_declName_2252_, v___x_2253_, v___x_2254_, v_a_2255_, v_val_2256_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2268_ = _args[0];
lean_object* v___x_2269_ = _args[1];
lean_object* v___x_2270_ = _args[2];
lean_object* v_declName_2271_ = _args[3];
lean_object* v___x_2272_ = _args[4];
lean_object* v___x_2273_ = _args[5];
lean_object* v_a_2274_ = _args[6];
lean_object* v_val_2275_ = _args[7];
lean_object* v_inst_2276_ = _args[8];
lean_object* v_R_2277_ = _args[9];
lean_object* v_a_2278_ = _args[10];
lean_object* v_b_2279_ = _args[11];
lean_object* v_c_2280_ = _args[12];
lean_object* v___y_2281_ = _args[13];
lean_object* v___y_2282_ = _args[14];
lean_object* v___y_2283_ = _args[15];
lean_object* v___y_2284_ = _args[16];
lean_object* v___y_2285_ = _args[17];
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2268_, v___x_2269_, v___x_2270_, v_declName_2271_, v___x_2272_, v___x_2273_, v_a_2274_, v_val_2275_, v_inst_2276_, v_R_2277_, v_a_2278_, v_b_2279_, v_c_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_val_2275_);
lean_dec(v_a_2274_);
lean_dec(v___x_2272_);
lean_dec(v_declName_2271_);
lean_dec_ref(v___x_2270_);
lean_dec(v___x_2269_);
lean_dec(v_upperBound_2268_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2287_, lean_object* v___y_2288_){
_start:
{
uint8_t v___x_2290_; 
v___x_2290_ = l_Lean_Expr_hasMVar(v_e_2287_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_e_2287_);
return v___x_2291_;
}
else
{
lean_object* v___x_2292_; lean_object* v_mctx_2293_; lean_object* v___x_2294_; lean_object* v_fst_2295_; lean_object* v_snd_2296_; lean_object* v___x_2297_; lean_object* v_cache_2298_; lean_object* v_zetaDeltaFVarIds_2299_; lean_object* v_postponed_2300_; lean_object* v_diag_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2310_; 
v___x_2292_ = lean_st_ref_get(v___y_2288_);
v_mctx_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_ref(v_mctx_2293_);
lean_dec(v___x_2292_);
v___x_2294_ = l_Lean_instantiateMVarsCore(v_mctx_2293_, v_e_2287_);
v_fst_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_fst_2295_);
v_snd_2296_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_snd_2296_);
lean_dec_ref(v___x_2294_);
v___x_2297_ = lean_st_ref_take(v___y_2288_);
v_cache_2298_ = lean_ctor_get(v___x_2297_, 1);
v_zetaDeltaFVarIds_2299_ = lean_ctor_get(v___x_2297_, 2);
v_postponed_2300_ = lean_ctor_get(v___x_2297_, 3);
v_diag_2301_ = lean_ctor_get(v___x_2297_, 4);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2297_, 0);
lean_dec(v_unused_2311_);
v___x_2303_ = v___x_2297_;
v_isShared_2304_ = v_isSharedCheck_2310_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_diag_2301_);
lean_inc(v_postponed_2300_);
lean_inc(v_zetaDeltaFVarIds_2299_);
lean_inc(v_cache_2298_);
lean_dec(v___x_2297_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2310_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v_snd_2296_);
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_snd_2296_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_cache_2298_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_zetaDeltaFVarIds_2299_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_postponed_2300_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_diag_2301_);
v___x_2306_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_st_ref_set(v___y_2288_, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_fst_2295_);
return v___x_2308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2312_, v___y_2313_);
lean_dec(v___y_2313_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2316_, v___y_2318_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_x_2340_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2347_, lean_object* v_e_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Meta_etaStruct_x3f(v_e_2348_, v_p_2347_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2374_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2374_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2374_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
if (lean_obj_tag(v_a_2355_) == 1)
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2369_; 
v_val_2359_ = lean_ctor_get(v_a_2355_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_a_2355_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2361_ = v_a_2355_;
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v_a_2355_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2369_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_val_2359_);
v___x_2364_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2364_);
v___x_2366_ = v___x_2357_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_dec(v_a_2355_);
v___x_2370_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2370_);
v___x_2372_ = v___x_2357_;
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
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2354_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2354_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2383_, lean_object* v_e_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2383_, v_e_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_apply_1(v_x_2392_, lean_box(0));
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2400_, v_x_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2408_, lean_object* v_b_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_dec(v_b_2409_);
lean_dec_ref(v_a_2408_);
return v_x_2410_;
}
else
{
lean_object* v_key_2411_; lean_object* v_value_2412_; lean_object* v_tail_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2425_; 
v_key_2411_ = lean_ctor_get(v_x_2410_, 0);
v_value_2412_ = lean_ctor_get(v_x_2410_, 1);
v_tail_2413_ = lean_ctor_get(v_x_2410_, 2);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_x_2410_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2415_ = v_x_2410_;
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_tail_2413_);
lean_inc(v_value_2412_);
lean_inc(v_key_2411_);
lean_dec(v_x_2410_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_ExprStructEq_beq(v_key_2411_, v_a_2408_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2408_, v_b_2409_, v_tail_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 2, v___x_2418_);
v___x_2420_ = v___x_2415_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_key_2411_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_value_2412_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
else
{
lean_object* v___x_2423_; 
lean_dec(v_value_2412_);
lean_dec(v_key_2411_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v_b_2409_);
lean_ctor_set(v___x_2415_, 0, v_a_2408_);
v___x_2423_ = v___x_2415_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2408_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_b_2409_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_tail_2413_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
return v_x_2426_;
}
else
{
lean_object* v_key_2428_; lean_object* v_value_2429_; lean_object* v_tail_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2453_; 
v_key_2428_ = lean_ctor_get(v_x_2427_, 0);
v_value_2429_ = lean_ctor_get(v_x_2427_, 1);
v_tail_2430_ = lean_ctor_get(v_x_2427_, 2);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_x_2427_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2432_ = v_x_2427_;
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_tail_2430_);
lean_inc(v_value_2429_);
lean_inc(v_key_2428_);
lean_dec(v_x_2427_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; uint64_t v_fold_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2434_ = lean_array_get_size(v_x_2426_);
v___x_2435_ = l_Lean_ExprStructEq_hash(v_key_2428_);
v___x_2436_ = 32ULL;
v___x_2437_ = lean_uint64_shift_right(v___x_2435_, v___x_2436_);
v_fold_2438_ = lean_uint64_xor(v___x_2435_, v___x_2437_);
v___x_2439_ = 16ULL;
v___x_2440_ = lean_uint64_shift_right(v_fold_2438_, v___x_2439_);
v___x_2441_ = lean_uint64_xor(v_fold_2438_, v___x_2440_);
v___x_2442_ = lean_uint64_to_usize(v___x_2441_);
v___x_2443_ = lean_usize_of_nat(v___x_2434_);
v___x_2444_ = ((size_t)1ULL);
v___x_2445_ = lean_usize_sub(v___x_2443_, v___x_2444_);
v___x_2446_ = lean_usize_land(v___x_2442_, v___x_2445_);
v___x_2447_ = lean_array_uget_borrowed(v_x_2426_, v___x_2446_);
lean_inc(v___x_2447_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 2, v___x_2447_);
v___x_2449_ = v___x_2432_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_key_2428_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_value_2429_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_array_uset(v_x_2426_, v___x_2446_, v___x_2449_);
v_x_2426_ = v___x_2450_;
v_x_2427_ = v_tail_2430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2454_, lean_object* v_source_2455_, lean_object* v_target_2456_){
_start:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_array_get_size(v_source_2455_);
v___x_2458_ = lean_nat_dec_lt(v_i_2454_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_source_2455_);
lean_dec(v_i_2454_);
return v_target_2456_;
}
else
{
lean_object* v_es_2459_; lean_object* v___x_2460_; lean_object* v_source_2461_; lean_object* v_target_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_es_2459_ = lean_array_fget(v_source_2455_, v_i_2454_);
v___x_2460_ = lean_box(0);
v_source_2461_ = lean_array_fset(v_source_2455_, v_i_2454_, v___x_2460_);
v_target_2462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2456_, v_es_2459_);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_add(v_i_2454_, v___x_2463_);
lean_dec(v_i_2454_);
v_i_2454_ = v___x_2464_;
v_source_2455_ = v_source_2461_;
v_target_2456_ = v_target_2462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_nbuckets_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2467_ = lean_array_get_size(v_data_2466_);
v___x_2468_ = lean_unsigned_to_nat(2u);
v_nbuckets_2469_ = lean_nat_mul(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_mk_array(v_nbuckets_2469_, v___x_2471_);
v___x_2473_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2470_, v_data_2466_, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2474_, lean_object* v_x_2475_){
_start:
{
if (lean_obj_tag(v_x_2475_) == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = 0;
return v___x_2476_;
}
else
{
lean_object* v_key_2477_; lean_object* v_tail_2478_; uint8_t v___x_2479_; 
v_key_2477_ = lean_ctor_get(v_x_2475_, 0);
v_tail_2478_ = lean_ctor_get(v_x_2475_, 2);
v___x_2479_ = l_Lean_ExprStructEq_beq(v_key_2477_, v_a_2474_);
if (v___x_2479_ == 0)
{
v_x_2475_ = v_tail_2478_;
goto _start;
}
else
{
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2481_, v_x_2482_);
lean_dec(v_x_2482_);
lean_dec_ref(v_a_2481_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2485_, lean_object* v_a_2486_, lean_object* v_b_2487_){
_start:
{
lean_object* v_size_2488_; lean_object* v_buckets_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2532_; 
v_size_2488_ = lean_ctor_get(v_m_2485_, 0);
v_buckets_2489_ = lean_ctor_get(v_m_2485_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_m_2485_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2491_ = v_m_2485_;
v_isShared_2492_ = v_isSharedCheck_2532_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_buckets_2489_);
lean_inc(v_size_2488_);
lean_dec(v_m_2485_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2532_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; uint64_t v_fold_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; lean_object* v_bkt_2506_; uint8_t v___x_2507_; 
v___x_2493_ = lean_array_get_size(v_buckets_2489_);
v___x_2494_ = l_Lean_ExprStructEq_hash(v_a_2486_);
v___x_2495_ = 32ULL;
v___x_2496_ = lean_uint64_shift_right(v___x_2494_, v___x_2495_);
v_fold_2497_ = lean_uint64_xor(v___x_2494_, v___x_2496_);
v___x_2498_ = 16ULL;
v___x_2499_ = lean_uint64_shift_right(v_fold_2497_, v___x_2498_);
v___x_2500_ = lean_uint64_xor(v_fold_2497_, v___x_2499_);
v___x_2501_ = lean_uint64_to_usize(v___x_2500_);
v___x_2502_ = lean_usize_of_nat(v___x_2493_);
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_sub(v___x_2502_, v___x_2503_);
v___x_2505_ = lean_usize_land(v___x_2501_, v___x_2504_);
v_bkt_2506_ = lean_array_uget_borrowed(v_buckets_2489_, v___x_2505_);
v___x_2507_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2486_, v_bkt_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v_size_x27_2509_; lean_object* v___x_2510_; lean_object* v_buckets_x27_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v___x_2508_ = lean_unsigned_to_nat(1u);
v_size_x27_2509_ = lean_nat_add(v_size_2488_, v___x_2508_);
lean_dec(v_size_2488_);
lean_inc(v_bkt_2506_);
v___x_2510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2486_);
lean_ctor_set(v___x_2510_, 1, v_b_2487_);
lean_ctor_set(v___x_2510_, 2, v_bkt_2506_);
v_buckets_x27_2511_ = lean_array_uset(v_buckets_2489_, v___x_2505_, v___x_2510_);
v___x_2512_ = lean_unsigned_to_nat(4u);
v___x_2513_ = lean_nat_mul(v_size_x27_2509_, v___x_2512_);
v___x_2514_ = lean_unsigned_to_nat(3u);
v___x_2515_ = lean_nat_div(v___x_2513_, v___x_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_array_get_size(v_buckets_x27_2511_);
v___x_2517_ = lean_nat_dec_le(v___x_2515_, v___x_2516_);
lean_dec(v___x_2515_);
if (v___x_2517_ == 0)
{
lean_object* v_val_2518_; lean_object* v___x_2520_; 
v_val_2518_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2511_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_val_2518_);
lean_ctor_set(v___x_2491_, 0, v_size_x27_2509_);
v___x_2520_ = v___x_2491_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_size_x27_2509_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_val_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
else
{
lean_object* v___x_2523_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_buckets_x27_2511_);
lean_ctor_set(v___x_2491_, 0, v_size_x27_2509_);
v___x_2523_ = v___x_2491_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_size_x27_2509_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_buckets_x27_2511_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v___x_2525_; lean_object* v_buckets_x27_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
lean_inc(v_bkt_2506_);
v___x_2525_ = lean_box(0);
v_buckets_x27_2526_ = lean_array_uset(v_buckets_2489_, v___x_2505_, v___x_2525_);
v___x_2527_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2486_, v_b_2487_, v_bkt_2506_);
v___x_2528_ = lean_array_uset(v_buckets_x27_2526_, v___x_2505_, v___x_2527_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v___x_2528_);
v___x_2530_ = v___x_2491_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_size_2488_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2533_, lean_object* v_e_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = lean_st_ref_take(v_a_2533_);
v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2537_, v_e_2534_, v_a_2535_);
v___x_2539_ = lean_st_ref_set(v_a_2533_, v___x_2538_);
v___x_2540_ = lean_box(0);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2541_, lean_object* v_e_2542_, lean_object* v_a_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2541_, v_e_2542_, v_a_2543_);
lean_dec(v_a_2541_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_apply_1(v_x_2547_, lean_box(0));
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2555_, v_x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2563_, lean_object* v_x_2564_){
_start:
{
if (lean_obj_tag(v_x_2564_) == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_box(0);
return v___x_2565_;
}
else
{
lean_object* v_key_2566_; lean_object* v_value_2567_; lean_object* v_tail_2568_; uint8_t v___x_2569_; 
v_key_2566_ = lean_ctor_get(v_x_2564_, 0);
v_value_2567_ = lean_ctor_get(v_x_2564_, 1);
v_tail_2568_ = lean_ctor_get(v_x_2564_, 2);
v___x_2569_ = l_Lean_ExprStructEq_beq(v_key_2566_, v_a_2563_);
if (v___x_2569_ == 0)
{
v_x_2564_ = v_tail_2568_;
goto _start;
}
else
{
lean_object* v___x_2571_; 
lean_inc(v_value_2567_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_value_2567_);
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2572_, v_x_2573_);
lean_dec(v_x_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_buckets_2577_; lean_object* v___x_2578_; uint64_t v___x_2579_; uint64_t v___x_2580_; uint64_t v___x_2581_; uint64_t v_fold_2582_; uint64_t v___x_2583_; uint64_t v___x_2584_; uint64_t v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_buckets_2577_ = lean_ctor_get(v_m_2575_, 1);
v___x_2578_ = lean_array_get_size(v_buckets_2577_);
v___x_2579_ = l_Lean_ExprStructEq_hash(v_a_2576_);
v___x_2580_ = 32ULL;
v___x_2581_ = lean_uint64_shift_right(v___x_2579_, v___x_2580_);
v_fold_2582_ = lean_uint64_xor(v___x_2579_, v___x_2581_);
v___x_2583_ = 16ULL;
v___x_2584_ = lean_uint64_shift_right(v_fold_2582_, v___x_2583_);
v___x_2585_ = lean_uint64_xor(v_fold_2582_, v___x_2584_);
v___x_2586_ = lean_uint64_to_usize(v___x_2585_);
v___x_2587_ = lean_usize_of_nat(v___x_2578_);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_sub(v___x_2587_, v___x_2588_);
v___x_2590_ = lean_usize_land(v___x_2586_, v___x_2589_);
v___x_2591_ = lean_array_uget_borrowed(v_buckets_2577_, v___x_2590_);
v___x_2592_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2576_, v___x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2593_, v_a_2594_);
lean_dec_ref(v_a_2594_);
lean_dec_ref(v_m_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2596_, lean_object* v___y_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2597_);
v___x_2604_ = lean_apply_7(v_k_2596_, v_b_2598_, v___y_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, lean_box(0));
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2605_, lean_object* v___y_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2605_, v___y_2606_, v_b_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2606_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2614_, uint8_t v_bi_2615_, lean_object* v_type_2616_, lean_object* v_k_2617_, uint8_t v_kind_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___f_2625_; lean_object* v___x_2626_; 
lean_inc(v___y_2619_);
v___f_2625_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2625_, 0, v_k_2617_);
lean_closure_set(v___f_2625_, 1, v___y_2619_);
v___x_2626_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2614_, v_bi_2615_, v_type_2616_, v___f_2625_, v_kind_2618_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2626_) == 0)
{
return v___x_2626_;
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2635_, lean_object* v_bi_2636_, lean_object* v_type_2637_, lean_object* v_k_2638_, lean_object* v_kind_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v_bi_boxed_2646_; uint8_t v_kind_boxed_2647_; lean_object* v_res_2648_; 
v_bi_boxed_2646_ = lean_unbox(v_bi_2636_);
v_kind_boxed_2647_ = lean_unbox(v_kind_2639_);
v_res_2648_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2635_, v_bi_boxed_2646_, v_type_2637_, v_k_2638_, v_kind_boxed_2647_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2649_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2663_, lean_object* v_type_2664_, lean_object* v_val_2665_, lean_object* v_k_2666_, uint8_t v_nondep_2667_, uint8_t v_kind_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___f_2675_; lean_object* v___x_2676_; 
lean_inc(v___y_2669_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2675_, 0, v_k_2666_);
lean_closure_set(v___f_2675_, 1, v___y_2669_);
v___x_2676_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2663_, v_type_2664_, v_val_2665_, v___f_2675_, v_nondep_2667_, v_kind_2668_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2676_) == 0)
{
return v___x_2676_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2676_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2676_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2685_, lean_object* v_type_2686_, lean_object* v_val_2687_, lean_object* v_k_2688_, lean_object* v_nondep_2689_, lean_object* v_kind_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v_nondep_boxed_2697_; uint8_t v_kind_boxed_2698_; lean_object* v_res_2699_; 
v_nondep_boxed_2697_ = lean_unbox(v_nondep_2689_);
v_kind_boxed_2698_ = lean_unbox(v_kind_2690_);
v_res_2699_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2685_, v_type_2686_, v_val_2687_, v_k_2688_, v_nondep_boxed_2697_, v_kind_boxed_2698_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
return v_res_2699_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = l_Lean_maxRecDepthErrorMessage;
v___x_2706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2708_ = l_Lean_MessageData_ofFormat(v___x_2707_);
return v___x_2708_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2710_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2711_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_ref_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___y_2728_; lean_object* v_fileName_2737_; lean_object* v_fileMap_2738_; lean_object* v_options_2739_; lean_object* v_currRecDepth_2740_; lean_object* v_maxRecDepth_2741_; lean_object* v_ref_2742_; lean_object* v_currNamespace_2743_; lean_object* v_openDecls_2744_; lean_object* v_initHeartbeats_2745_; lean_object* v_maxHeartbeats_2746_; lean_object* v_quotContext_2747_; lean_object* v_currMacroScope_2748_; uint8_t v_diag_2749_; lean_object* v_cancelTk_x3f_2750_; uint8_t v_suppressElabErrors_2751_; lean_object* v_inheritedTraceOptions_2752_; uint8_t v___x_2753_; 
v_fileName_2737_ = lean_ctor_get(v___y_2724_, 0);
lean_inc_ref(v_fileName_2737_);
v_fileMap_2738_ = lean_ctor_get(v___y_2724_, 1);
lean_inc_ref(v_fileMap_2738_);
v_options_2739_ = lean_ctor_get(v___y_2724_, 2);
lean_inc_ref(v_options_2739_);
v_currRecDepth_2740_ = lean_ctor_get(v___y_2724_, 3);
lean_inc(v_currRecDepth_2740_);
v_maxRecDepth_2741_ = lean_ctor_get(v___y_2724_, 4);
lean_inc(v_maxRecDepth_2741_);
v_ref_2742_ = lean_ctor_get(v___y_2724_, 5);
lean_inc(v_ref_2742_);
v_currNamespace_2743_ = lean_ctor_get(v___y_2724_, 6);
lean_inc(v_currNamespace_2743_);
v_openDecls_2744_ = lean_ctor_get(v___y_2724_, 7);
lean_inc(v_openDecls_2744_);
v_initHeartbeats_2745_ = lean_ctor_get(v___y_2724_, 8);
lean_inc(v_initHeartbeats_2745_);
v_maxHeartbeats_2746_ = lean_ctor_get(v___y_2724_, 9);
lean_inc(v_maxHeartbeats_2746_);
v_quotContext_2747_ = lean_ctor_get(v___y_2724_, 10);
lean_inc(v_quotContext_2747_);
v_currMacroScope_2748_ = lean_ctor_get(v___y_2724_, 11);
lean_inc(v_currMacroScope_2748_);
v_diag_2749_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*14);
v_cancelTk_x3f_2750_ = lean_ctor_get(v___y_2724_, 12);
lean_inc(v_cancelTk_x3f_2750_);
v_suppressElabErrors_2751_ = lean_ctor_get_uint8(v___y_2724_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2752_ = lean_ctor_get(v___y_2724_, 13);
lean_inc_ref(v_inheritedTraceOptions_2752_);
lean_dec_ref(v___y_2724_);
v___x_2753_ = lean_nat_dec_eq(v_currRecDepth_2740_, v_maxRecDepth_2741_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_currRecDepth_2740_, v___x_2754_);
lean_dec(v_currRecDepth_2740_);
v___x_2756_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2756_, 0, v_fileName_2737_);
lean_ctor_set(v___x_2756_, 1, v_fileMap_2738_);
lean_ctor_set(v___x_2756_, 2, v_options_2739_);
lean_ctor_set(v___x_2756_, 3, v___x_2755_);
lean_ctor_set(v___x_2756_, 4, v_maxRecDepth_2741_);
lean_ctor_set(v___x_2756_, 5, v_ref_2742_);
lean_ctor_set(v___x_2756_, 6, v_currNamespace_2743_);
lean_ctor_set(v___x_2756_, 7, v_openDecls_2744_);
lean_ctor_set(v___x_2756_, 8, v_initHeartbeats_2745_);
lean_ctor_set(v___x_2756_, 9, v_maxHeartbeats_2746_);
lean_ctor_set(v___x_2756_, 10, v_quotContext_2747_);
lean_ctor_set(v___x_2756_, 11, v_currMacroScope_2748_);
lean_ctor_set(v___x_2756_, 12, v_cancelTk_x3f_2750_);
lean_ctor_set(v___x_2756_, 13, v_inheritedTraceOptions_2752_);
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*14, v_diag_2749_);
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*14 + 1, v_suppressElabErrors_2751_);
lean_inc(v___y_2725_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
v___x_2757_ = lean_apply_6(v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___x_2756_, v___y_2725_, lean_box(0));
v___y_2728_ = v___x_2757_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2758_; 
lean_dec_ref(v_inheritedTraceOptions_2752_);
lean_dec(v_cancelTk_x3f_2750_);
lean_dec(v_currMacroScope_2748_);
lean_dec(v_quotContext_2747_);
lean_dec(v_maxHeartbeats_2746_);
lean_dec(v_initHeartbeats_2745_);
lean_dec(v_openDecls_2744_);
lean_dec(v_currNamespace_2743_);
lean_dec(v_maxRecDepth_2741_);
lean_dec(v_currRecDepth_2740_);
lean_dec_ref(v_options_2739_);
lean_dec_ref(v_fileMap_2738_);
lean_dec_ref(v_fileName_2737_);
lean_dec_ref(v_x_2720_);
v___x_2758_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2742_);
v___y_2728_ = v___x_2758_;
goto v___jp_2727_;
}
v___jp_2727_:
{
if (lean_obj_tag(v___y_2728_) == 0)
{
return v___y_2728_;
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
v_a_2729_ = lean_ctor_get(v___y_2728_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___y_2728_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___y_2728_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___y_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2769_, lean_object* v_pre_2770_, lean_object* v_post_2771_, uint8_t v_usedLetOnly_2772_, uint8_t v_skipConstInApp_2773_, uint8_t v_skipInstances_2774_, lean_object* v_body_2775_, lean_object* v_x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_array_push(v_fvars_2769_, v_x_2776_);
v___x_2784_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2770_, v_post_2771_, v_usedLetOnly_2772_, v_skipConstInApp_2773_, v_skipInstances_2774_, v___x_2783_, v_body_2775_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2785_, lean_object* v_pre_2786_, lean_object* v_post_2787_, lean_object* v_usedLetOnly_2788_, lean_object* v_skipConstInApp_2789_, lean_object* v_skipInstances_2790_, lean_object* v_body_2791_, lean_object* v_x_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v_usedLetOnly_boxed_2799_; uint8_t v_skipConstInApp_boxed_2800_; uint8_t v_skipInstances_boxed_2801_; lean_object* v_res_2802_; 
v_usedLetOnly_boxed_2799_ = lean_unbox(v_usedLetOnly_2788_);
v_skipConstInApp_boxed_2800_ = lean_unbox(v_skipConstInApp_2789_);
v_skipInstances_boxed_2801_ = lean_unbox(v_skipInstances_2790_);
v_res_2802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2785_, v_pre_2786_, v_post_2787_, v_usedLetOnly_boxed_2799_, v_skipConstInApp_boxed_2800_, v_skipInstances_boxed_2801_, v_body_2791_, v_x_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2803_, lean_object* v_post_2804_, uint8_t v_usedLetOnly_2805_, uint8_t v_skipConstInApp_2806_, uint8_t v_skipInstances_2807_, lean_object* v_e_2808_, lean_object* v_a_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
lean_inc_ref(v_post_2804_);
lean_inc(v___y_2813_);
lean_inc_ref(v___y_2812_);
lean_inc(v___y_2811_);
lean_inc_ref(v___y_2810_);
lean_inc_ref(v_e_2808_);
v___x_2815_ = lean_apply_6(v_post_2804_, v_e_2808_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, lean_box(0));
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2834_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2834_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2834_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
switch(lean_obj_tag(v_a_2816_))
{
case 0:
{
lean_object* v_e_2820_; lean_object* v___x_2822_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_post_2804_);
lean_dec_ref(v_pre_2803_);
v_e_2820_ = lean_ctor_get(v_a_2816_, 0);
lean_inc_ref(v_e_2820_);
lean_dec_ref(v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_e_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_e_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
case 1:
{
lean_object* v_e_2824_; lean_object* v___x_2825_; 
lean_del_object(v___x_2818_);
lean_dec_ref(v_e_2808_);
v_e_2824_ = lean_ctor_get(v_a_2816_, 0);
lean_inc_ref(v_e_2824_);
lean_dec_ref(v_a_2816_);
v___x_2825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2803_, v_post_2804_, v_usedLetOnly_2805_, v_skipConstInApp_2806_, v_skipInstances_2807_, v_e_2824_, v_a_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2825_;
}
default: 
{
lean_object* v_e_x3f_2826_; 
lean_dec_ref(v_post_2804_);
lean_dec_ref(v_pre_2803_);
v_e_x3f_2826_ = lean_ctor_get(v_a_2816_, 0);
lean_inc(v_e_x3f_2826_);
lean_dec_ref(v_a_2816_);
if (lean_obj_tag(v_e_x3f_2826_) == 0)
{
lean_object* v___x_2828_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_e_2808_);
v___x_2828_ = v___x_2818_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_e_2808_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
else
{
lean_object* v_val_2830_; lean_object* v___x_2832_; 
lean_dec_ref(v_e_2808_);
v_val_2830_ = lean_ctor_get(v_e_x3f_2826_, 0);
lean_inc(v_val_2830_);
lean_dec_ref(v_e_x3f_2826_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_val_2830_);
v___x_2832_ = v___x_2818_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_val_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_post_2804_);
lean_dec_ref(v_pre_2803_);
v_a_2835_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2815_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2815_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2843_, lean_object* v_post_2844_, uint8_t v_usedLetOnly_2845_, uint8_t v_skipConstInApp_2846_, uint8_t v_skipInstances_2847_, lean_object* v_fvars_2848_, lean_object* v_e_2849_, lean_object* v_a_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
if (lean_obj_tag(v_e_2849_) == 6)
{
lean_object* v_binderName_2856_; lean_object* v_binderType_2857_; lean_object* v_body_2858_; uint8_t v_binderInfo_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_binderName_2856_ = lean_ctor_get(v_e_2849_, 0);
lean_inc(v_binderName_2856_);
v_binderType_2857_ = lean_ctor_get(v_e_2849_, 1);
lean_inc_ref(v_binderType_2857_);
v_body_2858_ = lean_ctor_get(v_e_2849_, 2);
lean_inc_ref(v_body_2858_);
v_binderInfo_2859_ = lean_ctor_get_uint8(v_e_2849_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2849_);
v___x_2860_ = lean_expr_instantiate_rev(v_binderType_2857_, v_fvars_2848_);
lean_dec_ref(v_binderType_2857_);
lean_inc_ref(v_post_2844_);
lean_inc_ref(v_pre_2843_);
v___x_2861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2843_, v_post_2844_, v_usedLetOnly_2845_, v_skipConstInApp_2846_, v_skipInstances_2847_, v___x_2860_, v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___f_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = lean_box(v_usedLetOnly_2845_);
v___x_2864_ = lean_box(v_skipConstInApp_2846_);
v___x_2865_ = lean_box(v_skipInstances_2847_);
v___f_2866_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2866_, 0, v_fvars_2848_);
lean_closure_set(v___f_2866_, 1, v_pre_2843_);
lean_closure_set(v___f_2866_, 2, v_post_2844_);
lean_closure_set(v___f_2866_, 3, v___x_2863_);
lean_closure_set(v___f_2866_, 4, v___x_2864_);
lean_closure_set(v___f_2866_, 5, v___x_2865_);
lean_closure_set(v___f_2866_, 6, v_body_2858_);
v___x_2867_ = 0;
v___x_2868_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2856_, v_binderInfo_2859_, v_a_2862_, v___f_2866_, v___x_2867_, v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
return v___x_2868_;
}
else
{
lean_dec_ref(v_body_2858_);
lean_dec(v_binderName_2856_);
lean_dec_ref(v_fvars_2848_);
lean_dec_ref(v_post_2844_);
lean_dec_ref(v_pre_2843_);
return v___x_2861_;
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_expr_instantiate_rev(v_e_2849_, v_fvars_2848_);
lean_dec_ref(v_e_2849_);
lean_inc_ref(v_post_2844_);
lean_inc_ref(v_pre_2843_);
v___x_2870_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2843_, v_post_2844_, v_usedLetOnly_2845_, v_skipConstInApp_2846_, v_skipInstances_2847_, v___x_2869_, v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; uint8_t v___x_2872_; uint8_t v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = 0;
v___x_2873_ = 1;
v___x_2874_ = 1;
v___x_2875_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2848_, v_a_2871_, v___x_2872_, v_usedLetOnly_2845_, v___x_2872_, v___x_2873_, v___x_2874_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v_fvars_2848_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2843_, v_post_2844_, v_usedLetOnly_2845_, v_skipConstInApp_2846_, v_skipInstances_2847_, v_a_2876_, v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
return v___x_2877_;
}
else
{
lean_dec_ref(v_post_2844_);
lean_dec_ref(v_pre_2843_);
return v___x_2875_;
}
}
else
{
lean_dec_ref(v_fvars_2848_);
lean_dec_ref(v_post_2844_);
lean_dec_ref(v_pre_2843_);
return v___x_2870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2878_, lean_object* v_pre_2879_, lean_object* v_post_2880_, uint8_t v_usedLetOnly_2881_, uint8_t v_skipConstInApp_2882_, uint8_t v_skipInstances_2883_, lean_object* v_body_2884_, lean_object* v_x_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_array_push(v_fvars_2878_, v_x_2885_);
v___x_2893_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2879_, v_post_2880_, v_usedLetOnly_2881_, v_skipConstInApp_2882_, v_skipInstances_2883_, v___x_2892_, v_body_2884_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2894_, lean_object* v_pre_2895_, lean_object* v_post_2896_, lean_object* v_usedLetOnly_2897_, lean_object* v_skipConstInApp_2898_, lean_object* v_skipInstances_2899_, lean_object* v_body_2900_, lean_object* v_x_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
uint8_t v_usedLetOnly_boxed_2908_; uint8_t v_skipConstInApp_boxed_2909_; uint8_t v_skipInstances_boxed_2910_; lean_object* v_res_2911_; 
v_usedLetOnly_boxed_2908_ = lean_unbox(v_usedLetOnly_2897_);
v_skipConstInApp_boxed_2909_ = lean_unbox(v_skipConstInApp_2898_);
v_skipInstances_boxed_2910_ = lean_unbox(v_skipInstances_2899_);
v_res_2911_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2894_, v_pre_2895_, v_post_2896_, v_usedLetOnly_boxed_2908_, v_skipConstInApp_boxed_2909_, v_skipInstances_boxed_2910_, v_body_2900_, v_x_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2912_, lean_object* v_post_2913_, uint8_t v_usedLetOnly_2914_, uint8_t v_skipConstInApp_2915_, uint8_t v_skipInstances_2916_, lean_object* v_fvars_2917_, lean_object* v_e_2918_, lean_object* v_a_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
if (lean_obj_tag(v_e_2918_) == 8)
{
lean_object* v_declName_2925_; lean_object* v_type_2926_; lean_object* v_value_2927_; lean_object* v_body_2928_; uint8_t v_nondep_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_declName_2925_ = lean_ctor_get(v_e_2918_, 0);
lean_inc(v_declName_2925_);
v_type_2926_ = lean_ctor_get(v_e_2918_, 1);
lean_inc_ref(v_type_2926_);
v_value_2927_ = lean_ctor_get(v_e_2918_, 2);
lean_inc_ref(v_value_2927_);
v_body_2928_ = lean_ctor_get(v_e_2918_, 3);
lean_inc_ref(v_body_2928_);
v_nondep_2929_ = lean_ctor_get_uint8(v_e_2918_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2918_);
v___x_2930_ = lean_expr_instantiate_rev(v_type_2926_, v_fvars_2917_);
lean_dec_ref(v_type_2926_);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v___x_2930_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = lean_expr_instantiate_rev(v_value_2927_, v_fvars_2917_);
lean_dec_ref(v_value_2927_);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2934_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v___x_2933_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___f_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = lean_box(v_usedLetOnly_2914_);
v___x_2937_ = lean_box(v_skipConstInApp_2915_);
v___x_2938_ = lean_box(v_skipInstances_2916_);
v___f_2939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2939_, 0, v_fvars_2917_);
lean_closure_set(v___f_2939_, 1, v_pre_2912_);
lean_closure_set(v___f_2939_, 2, v_post_2913_);
lean_closure_set(v___f_2939_, 3, v___x_2936_);
lean_closure_set(v___f_2939_, 4, v___x_2937_);
lean_closure_set(v___f_2939_, 5, v___x_2938_);
lean_closure_set(v___f_2939_, 6, v_body_2928_);
v___x_2940_ = 0;
v___x_2941_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2925_, v_a_2932_, v_a_2935_, v___f_2939_, v_nondep_2929_, v___x_2940_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2941_;
}
else
{
lean_dec(v_a_2932_);
lean_dec_ref(v_body_2928_);
lean_dec(v_declName_2925_);
lean_dec_ref(v_fvars_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2934_;
}
}
else
{
lean_dec_ref(v_body_2928_);
lean_dec_ref(v_value_2927_);
lean_dec(v_declName_2925_);
lean_dec_ref(v_fvars_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2931_;
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_expr_instantiate_rev(v_e_2918_, v_fvars_2917_);
lean_dec_ref(v_e_2918_);
lean_inc_ref(v_post_2913_);
lean_inc_ref(v_pre_2912_);
v___x_2943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v___x_2942_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; uint8_t v___x_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = 0;
v___x_2946_ = 1;
v___x_2947_ = l_Lean_Meta_mkLetFVars(v_fvars_2917_, v_a_2944_, v_usedLetOnly_2914_, v___x_2945_, v___x_2946_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec_ref(v_fvars_2917_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2947_);
v___x_2949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2912_, v_post_2913_, v_usedLetOnly_2914_, v_skipConstInApp_2915_, v_skipInstances_2916_, v_a_2948_, v_a_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2949_;
}
else
{
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2947_;
}
}
else
{
lean_dec_ref(v_fvars_2917_);
lean_dec_ref(v_post_2913_);
lean_dec_ref(v_pre_2912_);
return v___x_2943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2950_, lean_object* v_post_2951_, uint8_t v_usedLetOnly_2952_, uint8_t v_skipConstInApp_2953_, uint8_t v_skipInstances_2954_, size_t v_sz_2955_, size_t v_i_2956_, lean_object* v_bs_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_usize_dec_lt(v_i_2956_, v_sz_2955_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref(v_post_2951_);
lean_dec_ref(v_pre_2950_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_bs_2957_);
return v___x_2965_;
}
else
{
lean_object* v_v_2966_; lean_object* v___x_2967_; 
v_v_2966_ = lean_array_uget_borrowed(v_bs_2957_, v_i_2956_);
lean_inc(v_v_2966_);
lean_inc_ref(v_post_2951_);
lean_inc_ref(v_pre_2950_);
v___x_2967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2950_, v_post_2951_, v_usedLetOnly_2952_, v_skipConstInApp_2953_, v_skipInstances_2954_, v_v_2966_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v_bs_x27_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v___x_2973_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = lean_unsigned_to_nat(0u);
v_bs_x27_2970_ = lean_array_uset(v_bs_2957_, v_i_2956_, v___x_2969_);
v___x_2971_ = ((size_t)1ULL);
v___x_2972_ = lean_usize_add(v_i_2956_, v___x_2971_);
v___x_2973_ = lean_array_uset(v_bs_x27_2970_, v_i_2956_, v_a_2968_);
v_i_2956_ = v___x_2972_;
v_bs_2957_ = v___x_2973_;
goto _start;
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_bs_2957_);
lean_dec_ref(v_post_2951_);
lean_dec_ref(v_pre_2950_);
v_a_2975_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2967_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2967_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_2983_, lean_object* v_post_2984_, uint8_t v_usedLetOnly_2985_, uint8_t v_skipConstInApp_2986_, uint8_t v_skipInstances_2987_, lean_object* v___x_2988_, lean_object* v___y_2989_, lean_object* v_b_2990_, lean_object* v_a_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2983_, v_post_2984_, v_usedLetOnly_2985_, v_skipConstInApp_2986_, v_skipInstances_2987_, v___x_2988_, v___y_2989_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3007_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3007_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3007_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3002_ = lean_array_fset(v_b_2990_, v_a_2991_, v_a_2998_);
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3003_);
v___x_3005_ = v___x_3000_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref(v_b_2990_);
v_a_3008_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2997_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2997_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3016_, lean_object* v_post_3017_, lean_object* v_usedLetOnly_3018_, lean_object* v_skipConstInApp_3019_, lean_object* v_skipInstances_3020_, lean_object* v___x_3021_, lean_object* v___y_3022_, lean_object* v_b_3023_, lean_object* v_a_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
uint8_t v_usedLetOnly_boxed_3030_; uint8_t v_skipConstInApp_boxed_3031_; uint8_t v_skipInstances_boxed_3032_; lean_object* v_res_3033_; 
v_usedLetOnly_boxed_3030_ = lean_unbox(v_usedLetOnly_3018_);
v_skipConstInApp_boxed_3031_ = lean_unbox(v_skipConstInApp_3019_);
v_skipInstances_boxed_3032_ = lean_unbox(v_skipInstances_3020_);
v_res_3033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3016_, v_post_3017_, v_usedLetOnly_boxed_3030_, v_skipConstInApp_boxed_3031_, v_skipInstances_boxed_3032_, v___x_3021_, v___y_3022_, v_b_3023_, v_a_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v_a_3024_);
lean_dec(v___y_3022_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3034_, lean_object* v___x_3035_, lean_object* v_pre_3036_, lean_object* v_post_3037_, uint8_t v_usedLetOnly_3038_, uint8_t v_skipConstInApp_3039_, uint8_t v_skipInstances_3040_, lean_object* v_a_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___y_3050_; uint8_t v___x_3073_; 
v___x_3073_ = lean_nat_dec_lt(v_a_3041_, v_upperBound_3034_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; 
lean_dec(v_a_3041_);
lean_dec_ref(v_post_3037_);
lean_dec_ref(v_pre_3036_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_b_3042_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = lean_array_fget_borrowed(v_b_3042_, v_a_3041_);
v___x_3076_ = lean_array_get_size(v___x_3035_);
v___x_3077_ = lean_nat_dec_lt(v_a_3041_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; 
lean_inc(v___x_3075_);
v___x_3078_ = lean_box(v_usedLetOnly_3038_);
v___x_3079_ = lean_box(v_skipConstInApp_3039_);
v___x_3080_ = lean_box(v_skipInstances_3040_);
lean_inc(v_a_3041_);
lean_inc(v___y_3043_);
lean_inc_ref(v_post_3037_);
lean_inc_ref(v_pre_3036_);
v___f_3081_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3081_, 0, v_pre_3036_);
lean_closure_set(v___f_3081_, 1, v_post_3037_);
lean_closure_set(v___f_3081_, 2, v___x_3078_);
lean_closure_set(v___f_3081_, 3, v___x_3079_);
lean_closure_set(v___f_3081_, 4, v___x_3080_);
lean_closure_set(v___f_3081_, 5, v___x_3075_);
lean_closure_set(v___f_3081_, 6, v___y_3043_);
lean_closure_set(v___f_3081_, 7, v_b_3042_);
lean_closure_set(v___f_3081_, 8, v_a_3041_);
v___y_3050_ = v___f_3081_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3082_; uint8_t v_isInstance_3083_; 
v___x_3082_ = lean_array_fget_borrowed(v___x_3035_, v_a_3041_);
v_isInstance_3083_ = lean_ctor_get_uint8(v___x_3082_, sizeof(void*)*1 + 4);
if (v_isInstance_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___f_3087_; 
lean_inc(v___x_3075_);
v___x_3084_ = lean_box(v_usedLetOnly_3038_);
v___x_3085_ = lean_box(v_skipConstInApp_3039_);
v___x_3086_ = lean_box(v_skipInstances_3040_);
lean_inc(v_a_3041_);
lean_inc(v___y_3043_);
lean_inc_ref(v_post_3037_);
lean_inc_ref(v_pre_3036_);
v___f_3087_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3087_, 0, v_pre_3036_);
lean_closure_set(v___f_3087_, 1, v_post_3037_);
lean_closure_set(v___f_3087_, 2, v___x_3084_);
lean_closure_set(v___f_3087_, 3, v___x_3085_);
lean_closure_set(v___f_3087_, 4, v___x_3086_);
lean_closure_set(v___f_3087_, 5, v___x_3075_);
lean_closure_set(v___f_3087_, 6, v___y_3043_);
lean_closure_set(v___f_3087_, 7, v_b_3042_);
lean_closure_set(v___f_3087_, 8, v_a_3041_);
v___y_3050_ = v___f_3087_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3088_; lean_object* v___f_3089_; 
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_b_3042_);
v___f_3089_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3089_, 0, v___x_3088_);
v___y_3050_ = v___f_3089_;
goto v___jp_3049_;
}
}
}
v___jp_3049_:
{
lean_object* v___x_3051_; 
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
v___x_3051_ = lean_apply_5(v___y_3050_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, lean_box(0));
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3064_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3064_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3064_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
if (lean_obj_tag(v_a_3052_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; 
lean_dec(v_a_3041_);
lean_dec_ref(v_post_3037_);
lean_dec_ref(v_pre_3036_);
v_a_3056_ = lean_ctor_get(v_a_3052_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v_a_3052_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v_a_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_del_object(v___x_3054_);
v_a_3060_ = lean_ctor_get(v_a_3052_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v_a_3052_);
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_add(v_a_3041_, v___x_3061_);
lean_dec(v_a_3041_);
v_a_3041_ = v___x_3062_;
v_b_3042_ = v_a_3060_;
goto _start;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v_a_3041_);
lean_dec_ref(v_post_3037_);
lean_dec_ref(v_pre_3036_);
v_a_3065_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3051_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3051_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3090_, lean_object* v_pre_3091_, lean_object* v_post_3092_, uint8_t v_usedLetOnly_3093_, uint8_t v_skipConstInApp_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_f_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; 
if (lean_obj_tag(v_x_3095_) == 5)
{
lean_object* v_fn_3153_; lean_object* v_arg_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_fn_3153_ = lean_ctor_get(v_x_3095_, 0);
lean_inc_ref(v_fn_3153_);
v_arg_3154_ = lean_ctor_get(v_x_3095_, 1);
lean_inc_ref(v_arg_3154_);
lean_dec_ref(v_x_3095_);
v___x_3155_ = lean_array_set(v_x_3096_, v_x_3097_, v_arg_3154_);
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_nat_sub(v_x_3097_, v___x_3156_);
lean_dec(v_x_3097_);
v_x_3095_ = v_fn_3153_;
v_x_3096_ = v___x_3155_;
v_x_3097_ = v___x_3157_;
goto _start;
}
else
{
lean_dec(v_x_3097_);
if (v_skipConstInApp_3094_ == 0)
{
goto v___jp_3150_;
}
else
{
uint8_t v___x_3159_; 
v___x_3159_ = l_Lean_Expr_isConst(v_x_3095_);
if (v___x_3159_ == 0)
{
goto v___jp_3150_;
}
else
{
v_f_3105_ = v_x_3095_;
v___y_3106_ = v___y_3098_;
v___y_3107_ = v___y_3099_;
v___y_3108_ = v___y_3100_;
v___y_3109_ = v___y_3101_;
v___y_3110_ = v___y_3102_;
goto v___jp_3104_;
}
}
}
v___jp_3104_:
{
if (v_skipInstances_3090_ == 0)
{
size_t v_sz_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v_sz_3111_ = lean_array_size(v_x_3096_);
v___x_3112_ = ((size_t)0ULL);
lean_inc_ref(v_post_3092_);
lean_inc_ref(v_pre_3091_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3091_, v_post_3092_, v_usedLetOnly_3093_, v_skipConstInApp_3094_, v_skipInstances_3090_, v_sz_3111_, v___x_3112_, v_x_3096_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = l_Lean_mkAppN(v_f_3105_, v_a_3114_);
lean_dec(v_a_3114_);
v___x_3116_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3091_, v_post_3092_, v_usedLetOnly_3093_, v_skipConstInApp_3094_, v_skipInstances_3090_, v___x_3115_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3116_;
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_f_3105_);
lean_dec_ref(v_post_3092_);
lean_dec_ref(v_pre_3091_);
v_a_3117_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3113_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3113_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = lean_array_get_size(v_x_3096_);
lean_inc_ref(v_f_3105_);
v___x_3126_ = l_Lean_Meta_getFunInfoNArgs(v_f_3105_, v___x_3125_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_paramInfo_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v_paramInfo_3128_ = lean_ctor_get(v_a_3127_, 0);
lean_inc_ref(v_paramInfo_3128_);
lean_dec(v_a_3127_);
v___x_3129_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3092_);
lean_inc_ref(v_pre_3091_);
v___x_3130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3125_, v_paramInfo_3128_, v_pre_3091_, v_post_3092_, v_usedLetOnly_3093_, v_skipConstInApp_3094_, v_skipInstances_3090_, v___x_3129_, v_x_3096_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec_ref(v_paramInfo_3128_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref(v___x_3130_);
v___x_3132_ = l_Lean_mkAppN(v_f_3105_, v_a_3131_);
lean_dec(v_a_3131_);
v___x_3133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3091_, v_post_3092_, v_usedLetOnly_3093_, v_skipConstInApp_3094_, v_skipInstances_3090_, v___x_3132_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3133_;
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v_f_3105_);
lean_dec_ref(v_post_3092_);
lean_dec_ref(v_pre_3091_);
v_a_3134_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3130_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3130_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec_ref(v_f_3105_);
lean_dec_ref(v_x_3096_);
lean_dec_ref(v_post_3092_);
lean_dec_ref(v_pre_3091_);
v_a_3142_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3126_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3126_);
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
}
v___jp_3150_:
{
lean_object* v___x_3151_; 
lean_inc_ref(v_post_3092_);
lean_inc_ref(v_pre_3091_);
v___x_3151_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3091_, v_post_3092_, v_usedLetOnly_3093_, v_skipConstInApp_3094_, v_skipInstances_3090_, v_x_3095_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref(v___x_3151_);
v_f_3105_ = v_a_3152_;
v___y_3106_ = v___y_3098_;
v___y_3107_ = v___y_3099_;
v___y_3108_ = v___y_3100_;
v___y_3109_ = v___y_3101_;
v___y_3110_ = v___y_3102_;
goto v___jp_3104_;
}
else
{
lean_dec_ref(v_x_3096_);
lean_dec_ref(v_post_3092_);
lean_dec_ref(v_pre_3091_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v_pre_3160_, lean_object* v_e_3161_, lean_object* v_post_3162_, uint8_t v_usedLetOnly_3163_, uint8_t v_skipConstInApp_3164_, uint8_t v_skipInstances_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
lean_inc_ref(v_pre_3160_);
lean_inc(v___y_3170_);
lean_inc_ref(v___y_3169_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
lean_inc_ref(v_e_3161_);
v___x_3172_ = lean_apply_6(v_pre_3160_, v_e_3161_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, lean_box(0));
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3221_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3221_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3221_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___y_3178_; 
switch(lean_obj_tag(v_a_3173_))
{
case 0:
{
lean_object* v_e_3213_; lean_object* v___x_3215_; 
lean_dec_ref(v_post_3162_);
lean_dec_ref(v_e_3161_);
lean_dec_ref(v_pre_3160_);
v_e_3213_ = lean_ctor_get(v_a_3173_, 0);
lean_inc_ref(v_e_3213_);
lean_dec_ref(v_a_3173_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v_e_3213_);
v___x_3215_ = v___x_3175_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_e_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
case 1:
{
lean_object* v_e_3217_; lean_object* v___x_3218_; 
lean_del_object(v___x_3175_);
lean_dec_ref(v_e_3161_);
v_e_3217_ = lean_ctor_get(v_a_3173_, 0);
lean_inc_ref(v_e_3217_);
lean_dec_ref(v_a_3173_);
v___x_3218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_e_3217_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3218_;
}
default: 
{
lean_object* v_e_x3f_3219_; 
lean_del_object(v___x_3175_);
v_e_x3f_3219_ = lean_ctor_get(v_a_3173_, 0);
lean_inc(v_e_x3f_3219_);
lean_dec_ref(v_a_3173_);
if (lean_obj_tag(v_e_x3f_3219_) == 0)
{
v___y_3178_ = v_e_3161_;
goto v___jp_3177_;
}
else
{
lean_object* v_val_3220_; 
lean_dec_ref(v_e_3161_);
v_val_3220_ = lean_ctor_get(v_e_x3f_3219_, 0);
lean_inc(v_val_3220_);
lean_dec_ref(v_e_x3f_3219_);
v___y_3178_ = v_val_3220_;
goto v___jp_3177_;
}
}
}
v___jp_3177_:
{
switch(lean_obj_tag(v___y_3178_))
{
case 7:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___x_3179_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3180_;
}
case 6:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___x_3181_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3182_;
}
case 8:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3184_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___x_3183_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3184_;
}
case 5:
{
lean_object* v_dummy_3185_; lean_object* v_nargs_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_dummy_3185_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3186_ = l_Lean_Expr_getAppNumArgs(v___y_3178_);
lean_inc(v_nargs_3186_);
v___x_3187_ = lean_mk_array(v_nargs_3186_, v_dummy_3185_);
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_nat_sub(v_nargs_3186_, v___x_3188_);
lean_dec(v_nargs_3186_);
v___x_3190_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3165_, v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v___y_3178_, v___x_3187_, v___x_3189_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3190_;
}
case 10:
{
lean_object* v_data_3191_; lean_object* v_expr_3192_; lean_object* v___x_3193_; 
v_data_3191_ = lean_ctor_get(v___y_3178_, 0);
v_expr_3192_ = lean_ctor_get(v___y_3178_, 1);
lean_inc_ref(v_expr_3192_);
lean_inc_ref(v_post_3162_);
lean_inc_ref(v_pre_3160_);
v___x_3193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_expr_3192_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; size_t v___x_3195_; size_t v___x_3196_; uint8_t v___x_3197_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = lean_ptr_addr(v_expr_3192_);
v___x_3196_ = lean_ptr_addr(v_a_3194_);
v___x_3197_ = lean_usize_dec_eq(v___x_3195_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_inc(v_data_3191_);
lean_dec_ref(v___y_3178_);
v___x_3198_ = l_Lean_Expr_mdata___override(v_data_3191_, v_a_3194_);
v___x_3199_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___x_3198_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; 
lean_dec(v_a_3194_);
v___x_3200_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3200_;
}
}
else
{
lean_dec_ref(v___y_3178_);
lean_dec_ref(v_post_3162_);
lean_dec_ref(v_pre_3160_);
return v___x_3193_;
}
}
case 11:
{
lean_object* v_typeName_3201_; lean_object* v_idx_3202_; lean_object* v_struct_3203_; lean_object* v___x_3204_; 
v_typeName_3201_ = lean_ctor_get(v___y_3178_, 0);
v_idx_3202_ = lean_ctor_get(v___y_3178_, 1);
v_struct_3203_ = lean_ctor_get(v___y_3178_, 2);
lean_inc_ref(v_struct_3203_);
lean_inc_ref(v_post_3162_);
lean_inc_ref(v_pre_3160_);
v___x_3204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_struct_3203_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; size_t v___x_3206_; size_t v___x_3207_; uint8_t v___x_3208_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_ptr_addr(v_struct_3203_);
v___x_3207_ = lean_ptr_addr(v_a_3205_);
v___x_3208_ = lean_usize_dec_eq(v___x_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_inc(v_idx_3202_);
lean_inc(v_typeName_3201_);
lean_dec_ref(v___y_3178_);
v___x_3209_ = l_Lean_Expr_proj___override(v_typeName_3201_, v_idx_3202_, v_a_3205_);
v___x_3210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___x_3209_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; 
lean_dec(v_a_3205_);
v___x_3211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3211_;
}
}
else
{
lean_dec_ref(v___y_3178_);
lean_dec_ref(v_post_3162_);
lean_dec_ref(v_pre_3160_);
return v___x_3204_;
}
}
default: 
{
lean_object* v___x_3212_; 
v___x_3212_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3160_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v___y_3178_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3212_;
}
}
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v_post_3162_);
lean_dec_ref(v_e_3161_);
lean_dec_ref(v_pre_3160_);
v_a_3222_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3172_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3172_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_3230_, lean_object* v_e_3231_, lean_object* v_post_3232_, lean_object* v_usedLetOnly_3233_, lean_object* v_skipConstInApp_3234_, lean_object* v_skipInstances_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
uint8_t v_usedLetOnly_boxed_3242_; uint8_t v_skipConstInApp_boxed_3243_; uint8_t v_skipInstances_boxed_3244_; lean_object* v_res_3245_; 
v_usedLetOnly_boxed_3242_ = lean_unbox(v_usedLetOnly_3233_);
v_skipConstInApp_boxed_3243_ = lean_unbox(v_skipConstInApp_3234_);
v_skipInstances_boxed_3244_ = lean_unbox(v_skipInstances_3235_);
v_res_3245_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v_pre_3230_, v_e_3231_, v_post_3232_, v_usedLetOnly_boxed_3242_, v_skipConstInApp_boxed_3243_, v_skipInstances_boxed_3244_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3246_, lean_object* v_post_3247_, uint8_t v_usedLetOnly_3248_, uint8_t v_skipConstInApp_3249_, uint8_t v_skipInstances_3250_, lean_object* v_e_3251_, lean_object* v_a_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_inc(v_a_3252_);
v___x_3258_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3258_, 0, lean_box(0));
lean_closure_set(v___x_3258_, 1, lean_box(0));
lean_closure_set(v___x_3258_, 2, v_a_3252_);
v___x_3259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3258_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3293_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3293_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3293_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3260_, v_e_3251_);
lean_dec(v_a_3260_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; 
lean_del_object(v___x_3262_);
v___x_3265_ = lean_box(v_usedLetOnly_3248_);
v___x_3266_ = lean_box(v_skipConstInApp_3249_);
v___x_3267_ = lean_box(v_skipInstances_3250_);
lean_inc_ref(v_e_3251_);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3268_, 0, v_pre_3246_);
lean_closure_set(v___f_3268_, 1, v_e_3251_);
lean_closure_set(v___f_3268_, 2, v_post_3247_);
lean_closure_set(v___f_3268_, 3, v___x_3265_);
lean_closure_set(v___f_3268_, 4, v___x_3266_);
lean_closure_set(v___f_3268_, 5, v___x_3267_);
lean_inc_ref(v___y_3255_);
v___x_3269_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3268_, v_a_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___f_3271_; lean_object* v___x_3272_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
lean_inc(v_a_3270_);
lean_inc(v_a_3252_);
v___f_3271_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3271_, 0, v_a_3252_);
lean_closure_set(v___f_3271_, 1, v_e_3251_);
lean_closure_set(v___f_3271_, 2, v_a_3270_);
v___x_3272_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3271_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3272_, 0);
lean_dec(v_unused_3280_);
v___x_3274_ = v___x_3272_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___x_3272_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_a_3270_);
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3270_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_a_3270_);
v_a_3281_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3272_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3272_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_dec_ref(v_e_3251_);
return v___x_3269_;
}
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3291_; 
lean_dec_ref(v_e_3251_);
lean_dec_ref(v_post_3247_);
lean_dec_ref(v_pre_3246_);
v_val_3289_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_val_3289_);
lean_dec_ref(v___x_3264_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_val_3289_);
v___x_3291_ = v___x_3262_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_val_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec_ref(v_e_3251_);
lean_dec_ref(v_post_3247_);
lean_dec_ref(v_pre_3246_);
v_a_3294_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3259_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3259_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_3302_, lean_object* v_pre_3303_, lean_object* v_post_3304_, lean_object* v_usedLetOnly_3305_, lean_object* v_skipConstInApp_3306_, lean_object* v_skipInstances_3307_, lean_object* v_body_3308_, lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
uint8_t v_usedLetOnly_boxed_3316_; uint8_t v_skipConstInApp_boxed_3317_; uint8_t v_skipInstances_boxed_3318_; lean_object* v_res_3319_; 
v_usedLetOnly_boxed_3316_ = lean_unbox(v_usedLetOnly_3305_);
v_skipConstInApp_boxed_3317_ = lean_unbox(v_skipConstInApp_3306_);
v_skipInstances_boxed_3318_ = lean_unbox(v_skipInstances_3307_);
v_res_3319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_3302_, v_pre_3303_, v_post_3304_, v_usedLetOnly_boxed_3316_, v_skipConstInApp_boxed_3317_, v_skipInstances_boxed_3318_, v_body_3308_, v_x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3320_, lean_object* v_post_3321_, uint8_t v_usedLetOnly_3322_, uint8_t v_skipConstInApp_3323_, uint8_t v_skipInstances_3324_, lean_object* v_fvars_3325_, lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
if (lean_obj_tag(v_e_3326_) == 7)
{
lean_object* v_binderName_3333_; lean_object* v_binderType_3334_; lean_object* v_body_3335_; uint8_t v_binderInfo_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_binderName_3333_ = lean_ctor_get(v_e_3326_, 0);
lean_inc(v_binderName_3333_);
v_binderType_3334_ = lean_ctor_get(v_e_3326_, 1);
lean_inc_ref(v_binderType_3334_);
v_body_3335_ = lean_ctor_get(v_e_3326_, 2);
lean_inc_ref(v_body_3335_);
v_binderInfo_3336_ = lean_ctor_get_uint8(v_e_3326_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3326_);
v___x_3337_ = lean_expr_instantiate_rev(v_binderType_3334_, v_fvars_3325_);
lean_dec_ref(v_binderType_3334_);
lean_inc_ref(v_post_3321_);
lean_inc_ref(v_pre_3320_);
v___x_3338_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3320_, v_post_3321_, v_usedLetOnly_3322_, v_skipConstInApp_3323_, v_skipInstances_3324_, v___x_3337_, v_a_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___f_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = lean_box(v_usedLetOnly_3322_);
v___x_3341_ = lean_box(v_skipConstInApp_3323_);
v___x_3342_ = lean_box(v_skipInstances_3324_);
v___f_3343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3343_, 0, v_fvars_3325_);
lean_closure_set(v___f_3343_, 1, v_pre_3320_);
lean_closure_set(v___f_3343_, 2, v_post_3321_);
lean_closure_set(v___f_3343_, 3, v___x_3340_);
lean_closure_set(v___f_3343_, 4, v___x_3341_);
lean_closure_set(v___f_3343_, 5, v___x_3342_);
lean_closure_set(v___f_3343_, 6, v_body_3335_);
v___x_3344_ = 0;
v___x_3345_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3333_, v_binderInfo_3336_, v_a_3339_, v___f_3343_, v___x_3344_, v_a_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3345_;
}
else
{
lean_dec_ref(v_body_3335_);
lean_dec(v_binderName_3333_);
lean_dec_ref(v_fvars_3325_);
lean_dec_ref(v_post_3321_);
lean_dec_ref(v_pre_3320_);
return v___x_3338_;
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_expr_instantiate_rev(v_e_3326_, v_fvars_3325_);
lean_dec_ref(v_e_3326_);
lean_inc_ref(v_post_3321_);
lean_inc_ref(v_pre_3320_);
v___x_3347_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3320_, v_post_3321_, v_usedLetOnly_3322_, v_skipConstInApp_3323_, v_skipInstances_3324_, v___x_3346_, v_a_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; uint8_t v___x_3349_; uint8_t v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = 0;
v___x_3350_ = 1;
v___x_3351_ = 1;
v___x_3352_ = l_Lean_Meta_mkForallFVars(v_fvars_3325_, v_a_3348_, v___x_3349_, v_usedLetOnly_3322_, v___x_3350_, v___x_3351_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec_ref(v_fvars_3325_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3320_, v_post_3321_, v_usedLetOnly_3322_, v_skipConstInApp_3323_, v_skipInstances_3324_, v_a_3353_, v_a_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3354_;
}
else
{
lean_dec_ref(v_post_3321_);
lean_dec_ref(v_pre_3320_);
return v___x_3352_;
}
}
else
{
lean_dec_ref(v_fvars_3325_);
lean_dec_ref(v_post_3321_);
lean_dec_ref(v_pre_3320_);
return v___x_3347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3355_, lean_object* v_pre_3356_, lean_object* v_post_3357_, uint8_t v_usedLetOnly_3358_, uint8_t v_skipConstInApp_3359_, uint8_t v_skipInstances_3360_, lean_object* v_body_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_array_push(v_fvars_3355_, v_x_3362_);
v___x_3370_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3356_, v_post_3357_, v_usedLetOnly_3358_, v_skipConstInApp_3359_, v_skipInstances_3360_, v___x_3369_, v_body_3361_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3371_, lean_object* v_post_3372_, lean_object* v_usedLetOnly_3373_, lean_object* v_skipConstInApp_3374_, lean_object* v_skipInstances_3375_, lean_object* v_e_3376_, lean_object* v_a_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
uint8_t v_usedLetOnly_boxed_3383_; uint8_t v_skipConstInApp_boxed_3384_; uint8_t v_skipInstances_boxed_3385_; lean_object* v_res_3386_; 
v_usedLetOnly_boxed_3383_ = lean_unbox(v_usedLetOnly_3373_);
v_skipConstInApp_boxed_3384_ = lean_unbox(v_skipConstInApp_3374_);
v_skipInstances_boxed_3385_ = lean_unbox(v_skipInstances_3375_);
v_res_3386_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3371_, v_post_3372_, v_usedLetOnly_boxed_3383_, v_skipConstInApp_boxed_3384_, v_skipInstances_boxed_3385_, v_e_3376_, v_a_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v_a_3377_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3387_, lean_object* v_post_3388_, lean_object* v_usedLetOnly_3389_, lean_object* v_skipConstInApp_3390_, lean_object* v_skipInstances_3391_, lean_object* v_sz_3392_, lean_object* v_i_3393_, lean_object* v_bs_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
uint8_t v_usedLetOnly_boxed_3401_; uint8_t v_skipConstInApp_boxed_3402_; uint8_t v_skipInstances_boxed_3403_; size_t v_sz_boxed_3404_; size_t v_i_boxed_3405_; lean_object* v_res_3406_; 
v_usedLetOnly_boxed_3401_ = lean_unbox(v_usedLetOnly_3389_);
v_skipConstInApp_boxed_3402_ = lean_unbox(v_skipConstInApp_3390_);
v_skipInstances_boxed_3403_ = lean_unbox(v_skipInstances_3391_);
v_sz_boxed_3404_ = lean_unbox_usize(v_sz_3392_);
lean_dec(v_sz_3392_);
v_i_boxed_3405_ = lean_unbox_usize(v_i_3393_);
lean_dec(v_i_3393_);
v_res_3406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3387_, v_post_3388_, v_usedLetOnly_boxed_3401_, v_skipConstInApp_boxed_3402_, v_skipInstances_boxed_3403_, v_sz_boxed_3404_, v_i_boxed_3405_, v_bs_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3407_, lean_object* v_post_3408_, lean_object* v_usedLetOnly_3409_, lean_object* v_skipConstInApp_3410_, lean_object* v_skipInstances_3411_, lean_object* v_e_3412_, lean_object* v_a_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v_usedLetOnly_boxed_3419_; uint8_t v_skipConstInApp_boxed_3420_; uint8_t v_skipInstances_boxed_3421_; lean_object* v_res_3422_; 
v_usedLetOnly_boxed_3419_ = lean_unbox(v_usedLetOnly_3409_);
v_skipConstInApp_boxed_3420_ = lean_unbox(v_skipConstInApp_3410_);
v_skipInstances_boxed_3421_ = lean_unbox(v_skipInstances_3411_);
v_res_3422_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3407_, v_post_3408_, v_usedLetOnly_boxed_3419_, v_skipConstInApp_boxed_3420_, v_skipInstances_boxed_3421_, v_e_3412_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v_a_3413_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3423_, lean_object* v_post_3424_, lean_object* v_usedLetOnly_3425_, lean_object* v_skipConstInApp_3426_, lean_object* v_skipInstances_3427_, lean_object* v_fvars_3428_, lean_object* v_e_3429_, lean_object* v_a_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v_usedLetOnly_boxed_3436_; uint8_t v_skipConstInApp_boxed_3437_; uint8_t v_skipInstances_boxed_3438_; lean_object* v_res_3439_; 
v_usedLetOnly_boxed_3436_ = lean_unbox(v_usedLetOnly_3425_);
v_skipConstInApp_boxed_3437_ = lean_unbox(v_skipConstInApp_3426_);
v_skipInstances_boxed_3438_ = lean_unbox(v_skipInstances_3427_);
v_res_3439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3423_, v_post_3424_, v_usedLetOnly_boxed_3436_, v_skipConstInApp_boxed_3437_, v_skipInstances_boxed_3438_, v_fvars_3428_, v_e_3429_, v_a_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v_a_3430_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3440_, lean_object* v_post_3441_, lean_object* v_usedLetOnly_3442_, lean_object* v_skipConstInApp_3443_, lean_object* v_skipInstances_3444_, lean_object* v_fvars_3445_, lean_object* v_e_3446_, lean_object* v_a_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v_usedLetOnly_boxed_3453_; uint8_t v_skipConstInApp_boxed_3454_; uint8_t v_skipInstances_boxed_3455_; lean_object* v_res_3456_; 
v_usedLetOnly_boxed_3453_ = lean_unbox(v_usedLetOnly_3442_);
v_skipConstInApp_boxed_3454_ = lean_unbox(v_skipConstInApp_3443_);
v_skipInstances_boxed_3455_ = lean_unbox(v_skipInstances_3444_);
v_res_3456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3440_, v_post_3441_, v_usedLetOnly_boxed_3453_, v_skipConstInApp_boxed_3454_, v_skipInstances_boxed_3455_, v_fvars_3445_, v_e_3446_, v_a_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v_a_3447_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3457_, lean_object* v_post_3458_, lean_object* v_usedLetOnly_3459_, lean_object* v_skipConstInApp_3460_, lean_object* v_skipInstances_3461_, lean_object* v_fvars_3462_, lean_object* v_e_3463_, lean_object* v_a_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v_usedLetOnly_boxed_3470_; uint8_t v_skipConstInApp_boxed_3471_; uint8_t v_skipInstances_boxed_3472_; lean_object* v_res_3473_; 
v_usedLetOnly_boxed_3470_ = lean_unbox(v_usedLetOnly_3459_);
v_skipConstInApp_boxed_3471_ = lean_unbox(v_skipConstInApp_3460_);
v_skipInstances_boxed_3472_ = lean_unbox(v_skipInstances_3461_);
v_res_3473_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3457_, v_post_3458_, v_usedLetOnly_boxed_3470_, v_skipConstInApp_boxed_3471_, v_skipInstances_boxed_3472_, v_fvars_3462_, v_e_3463_, v_a_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v_a_3464_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3474_, lean_object* v___x_3475_, lean_object* v_pre_3476_, lean_object* v_post_3477_, lean_object* v_usedLetOnly_3478_, lean_object* v_skipConstInApp_3479_, lean_object* v_skipInstances_3480_, lean_object* v_a_3481_, lean_object* v_b_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
uint8_t v_usedLetOnly_boxed_3489_; uint8_t v_skipConstInApp_boxed_3490_; uint8_t v_skipInstances_boxed_3491_; lean_object* v_res_3492_; 
v_usedLetOnly_boxed_3489_ = lean_unbox(v_usedLetOnly_3478_);
v_skipConstInApp_boxed_3490_ = lean_unbox(v_skipConstInApp_3479_);
v_skipInstances_boxed_3491_ = lean_unbox(v_skipInstances_3480_);
v_res_3492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3474_, v___x_3475_, v_pre_3476_, v_post_3477_, v_usedLetOnly_boxed_3489_, v_skipConstInApp_boxed_3490_, v_skipInstances_boxed_3491_, v_a_3481_, v_b_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___x_3475_);
lean_dec(v_upperBound_3474_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3493_, lean_object* v_pre_3494_, lean_object* v_post_3495_, lean_object* v_usedLetOnly_3496_, lean_object* v_skipConstInApp_3497_, lean_object* v_x_3498_, lean_object* v_x_3499_, lean_object* v_x_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v_skipInstances_boxed_3507_; uint8_t v_usedLetOnly_boxed_3508_; uint8_t v_skipConstInApp_boxed_3509_; lean_object* v_res_3510_; 
v_skipInstances_boxed_3507_ = lean_unbox(v_skipInstances_3493_);
v_usedLetOnly_boxed_3508_ = lean_unbox(v_usedLetOnly_3496_);
v_skipConstInApp_boxed_3509_ = lean_unbox(v_skipConstInApp_3497_);
v_res_3510_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3507_, v_pre_3494_, v_post_3495_, v_usedLetOnly_boxed_3508_, v_skipConstInApp_boxed_3509_, v_x_3498_, v_x_3499_, v_x_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
return v_res_3510_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_unsigned_to_nat(16u);
v___x_3513_ = lean_mk_array(v___x_3512_, v___x_3511_);
return v___x_3513_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
lean_ctor_set(v___x_3516_, 1, v___x_3514_);
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3518_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3518_, 0, lean_box(0));
lean_closure_set(v___x_3518_, 1, lean_box(0));
lean_closure_set(v___x_3518_, 2, v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3519_, lean_object* v_pre_3520_, lean_object* v_post_3521_, uint8_t v_usedLetOnly_3522_, uint8_t v_skipConstInApp_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_a_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3529_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3530_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3529_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = 0;
v___x_3533_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3520_, v_post_3521_, v_usedLetOnly_3522_, v_skipConstInApp_3523_, v___x_3532_, v_input_3519_, v_a_3531_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3533_);
v___x_3535_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3535_, 0, lean_box(0));
lean_closure_set(v___x_3535_, 1, lean_box(0));
lean_closure_set(v___x_3535_, 2, v_a_3531_);
v___x_3536_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3535_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3536_, 0);
lean_dec(v_unused_3544_);
v___x_3538_ = v___x_3536_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v___x_3536_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 0, v_a_3534_);
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3534_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_dec(v_a_3531_);
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3545_, lean_object* v_pre_3546_, lean_object* v_post_3547_, lean_object* v_usedLetOnly_3548_, lean_object* v_skipConstInApp_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
uint8_t v_usedLetOnly_boxed_3555_; uint8_t v_skipConstInApp_boxed_3556_; lean_object* v_res_3557_; 
v_usedLetOnly_boxed_3555_ = lean_unbox(v_usedLetOnly_3548_);
v_skipConstInApp_boxed_3556_ = lean_unbox(v_skipConstInApp_3549_);
v_res_3557_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3545_, v_pre_3546_, v_post_3547_, v_usedLetOnly_boxed_3555_, v_skipConstInApp_boxed_3556_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3559_, lean_object* v_p_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v_a_3567_; lean_object* v___f_3568_; lean_object* v___f_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; 
v___x_3566_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3559_, v_a_3562_);
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
v___f_3568_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3569_, 0, v_p_3560_);
v___x_3570_ = 0;
v___x_3571_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3567_, v___f_3568_, v___f_3569_, v___x_3570_, v___x_3570_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3572_, lean_object* v_p_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_Meta_etaStructReduce(v_e_3572_, v_p_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3580_, lean_object* v___x_3581_, lean_object* v_pre_3582_, lean_object* v_post_3583_, uint8_t v_usedLetOnly_3584_, uint8_t v_skipConstInApp_3585_, uint8_t v_skipInstances_3586_, lean_object* v___x_3587_, lean_object* v_inst_3588_, lean_object* v_R_3589_, lean_object* v_a_3590_, lean_object* v_b_3591_, lean_object* v_c_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3580_, v___x_3581_, v_pre_3582_, v_post_3583_, v_usedLetOnly_3584_, v_skipConstInApp_3585_, v_skipInstances_3586_, v_a_3590_, v_b_3591_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3600_ = _args[0];
lean_object* v___x_3601_ = _args[1];
lean_object* v_pre_3602_ = _args[2];
lean_object* v_post_3603_ = _args[3];
lean_object* v_usedLetOnly_3604_ = _args[4];
lean_object* v_skipConstInApp_3605_ = _args[5];
lean_object* v_skipInstances_3606_ = _args[6];
lean_object* v___x_3607_ = _args[7];
lean_object* v_inst_3608_ = _args[8];
lean_object* v_R_3609_ = _args[9];
lean_object* v_a_3610_ = _args[10];
lean_object* v_b_3611_ = _args[11];
lean_object* v_c_3612_ = _args[12];
lean_object* v___y_3613_ = _args[13];
lean_object* v___y_3614_ = _args[14];
lean_object* v___y_3615_ = _args[15];
lean_object* v___y_3616_ = _args[16];
lean_object* v___y_3617_ = _args[17];
lean_object* v___y_3618_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3619_; uint8_t v_skipConstInApp_boxed_3620_; uint8_t v_skipInstances_boxed_3621_; lean_object* v_res_3622_; 
v_usedLetOnly_boxed_3619_ = lean_unbox(v_usedLetOnly_3604_);
v_skipConstInApp_boxed_3620_ = lean_unbox(v_skipConstInApp_3605_);
v_skipInstances_boxed_3621_ = lean_unbox(v_skipInstances_3606_);
v_res_3622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3600_, v___x_3601_, v_pre_3602_, v_post_3603_, v_usedLetOnly_boxed_3619_, v_skipConstInApp_boxed_3620_, v_skipInstances_boxed_3621_, v___x_3607_, v_inst_3608_, v_R_3609_, v_a_3610_, v_b_3611_, v_c_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec(v___x_3607_);
lean_dec_ref(v___x_3601_);
lean_dec(v_upperBound_3600_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3623_, lean_object* v_m_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3624_, v_a_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3627_, lean_object* v_m_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3627_, v_m_3628_, v_a_3629_);
lean_dec_ref(v_a_3629_);
lean_dec_ref(v_m_3628_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3631_, lean_object* v_name_3632_, uint8_t v_bi_3633_, lean_object* v_type_3634_, lean_object* v_k_3635_, uint8_t v_kind_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3632_, v_bi_3633_, v_type_3634_, v_k_3635_, v_kind_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3644_, lean_object* v_name_3645_, lean_object* v_bi_3646_, lean_object* v_type_3647_, lean_object* v_k_3648_, lean_object* v_kind_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_bi_boxed_3656_; uint8_t v_kind_boxed_3657_; lean_object* v_res_3658_; 
v_bi_boxed_3656_ = lean_unbox(v_bi_3646_);
v_kind_boxed_3657_ = lean_unbox(v_kind_3649_);
v_res_3658_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3644_, v_name_3645_, v_bi_boxed_3656_, v_type_3647_, v_k_3648_, v_kind_boxed_3657_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3659_, lean_object* v_name_3660_, lean_object* v_type_3661_, lean_object* v_val_3662_, lean_object* v_k_3663_, uint8_t v_nondep_3664_, uint8_t v_kind_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3660_, v_type_3661_, v_val_3662_, v_k_3663_, v_nondep_3664_, v_kind_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3673_, lean_object* v_name_3674_, lean_object* v_type_3675_, lean_object* v_val_3676_, lean_object* v_k_3677_, lean_object* v_nondep_3678_, lean_object* v_kind_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
uint8_t v_nondep_boxed_3686_; uint8_t v_kind_boxed_3687_; lean_object* v_res_3688_; 
v_nondep_boxed_3686_ = lean_unbox(v_nondep_3678_);
v_kind_boxed_3687_ = lean_unbox(v_kind_3679_);
v_res_3688_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3673_, v_name_3674_, v_type_3675_, v_val_3676_, v_k_3677_, v_nondep_boxed_3686_, v_kind_boxed_3687_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3689_, lean_object* v_ref_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3690_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3697_, lean_object* v_ref_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3697_, v_ref_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3705_, lean_object* v_x_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___x_3713_; 
lean_inc_ref(v___y_3710_);
v___x_3713_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3714_, lean_object* v_x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3714_, v_x_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3723_, lean_object* v_m_3724_, lean_object* v_a_3725_, lean_object* v_b_3726_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3724_, v_a_3725_, v_b_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3728_, lean_object* v_a_3729_, lean_object* v_x_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3729_, v_x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3732_, lean_object* v_a_3733_, lean_object* v_x_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3732_, v_a_3733_, v_x_3734_);
lean_dec(v_x_3734_);
lean_dec_ref(v_a_3733_);
return v_res_3735_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3736_, lean_object* v_a_3737_, lean_object* v_x_3738_){
_start:
{
uint8_t v___x_3739_; 
v___x_3739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3737_, v_x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3740_, lean_object* v_a_3741_, lean_object* v_x_3742_){
_start:
{
uint8_t v_res_3743_; lean_object* v_r_3744_; 
v_res_3743_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3740_, v_a_3741_, v_x_3742_);
lean_dec(v_x_3742_);
lean_dec_ref(v_a_3741_);
v_r_3744_ = lean_box(v_res_3743_);
return v_r_3744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3745_, lean_object* v_data_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3748_, lean_object* v_a_3749_, lean_object* v_b_3750_, lean_object* v_x_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3749_, v_b_3750_, v_x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3753_, lean_object* v_i_3754_, lean_object* v_source_3755_, lean_object* v_target_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3754_, v_source_3755_, v_target_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3758_, lean_object* v_x_3759_, lean_object* v_x_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3759_, v_x_3760_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3762_, lean_object* v_inst_3763_, lean_object* v_toBind_3764_, lean_object* v___f_3765_, lean_object* v_____do__lift_3766_){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3767_, 0, v_____do__lift_3766_);
lean_closure_set(v___x_3767_, 1, v_binderType_3762_);
v___x_3768_ = lean_apply_2(v_inst_3763_, lean_box(0), v___x_3767_);
v___x_3769_ = lean_apply_4(v_toBind_3764_, lean_box(0), lean_box(0), v___x_3768_, v___f_3765_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3770_, lean_object* v_usedFields_3771_, lean_object* v_binderName_3772_, lean_object* v_body_3773_, lean_object* v_val_3774_, lean_object* v_inst_3775_, lean_object* v_inst_3776_, lean_object* v_fieldVal_x3f_3777_, lean_object* v_____do__lift_3778_){
_start:
{
uint8_t v_____do__lift_469__boxed_3779_; lean_object* v_res_3780_; 
v_____do__lift_469__boxed_3779_ = lean_unbox(v_____do__lift_3778_);
v_res_3780_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3770_, v_usedFields_3771_, v_binderName_3772_, v_body_3773_, v_val_3774_, v_inst_3775_, v_inst_3776_, v_fieldVal_x3f_3777_, v_____do__lift_469__boxed_3779_);
lean_dec_ref(v_val_3774_);
lean_dec_ref(v_body_3773_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3781_, lean_object* v_usedFields_3782_, lean_object* v_binderName_3783_, lean_object* v_body_3784_, lean_object* v_inst_3785_, lean_object* v_inst_3786_, lean_object* v_fieldVal_x3f_3787_, lean_object* v_binderType_3788_, lean_object* v_toBind_3789_, lean_object* v_____x_3790_){
_start:
{
if (lean_obj_tag(v_____x_3790_) == 1)
{
lean_object* v_val_3791_; lean_object* v___f_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_val_3791_ = lean_ctor_get(v_____x_3790_, 0);
lean_inc(v_val_3791_);
lean_dec_ref(v_____x_3790_);
lean_inc(v_inst_3786_);
lean_inc(v_val_3791_);
v___f_3792_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3792_, 0, v_toPure_3781_);
lean_closure_set(v___f_3792_, 1, v_usedFields_3782_);
lean_closure_set(v___f_3792_, 2, v_binderName_3783_);
lean_closure_set(v___f_3792_, 3, v_body_3784_);
lean_closure_set(v___f_3792_, 4, v_val_3791_);
lean_closure_set(v___f_3792_, 5, v_inst_3785_);
lean_closure_set(v___f_3792_, 6, v_inst_3786_);
lean_closure_set(v___f_3792_, 7, v_fieldVal_x3f_3787_);
lean_inc(v_toBind_3789_);
lean_inc(v_inst_3786_);
v___f_3793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3793_, 0, v_binderType_3788_);
lean_closure_set(v___f_3793_, 1, v_inst_3786_);
lean_closure_set(v___f_3793_, 2, v_toBind_3789_);
lean_closure_set(v___f_3793_, 3, v___f_3792_);
v___x_3794_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3794_, 0, v_val_3791_);
v___x_3795_ = lean_apply_2(v_inst_3786_, lean_box(0), v___x_3794_);
v___x_3796_ = lean_apply_4(v_toBind_3789_, lean_box(0), lean_box(0), v___x_3795_, v___f_3793_);
return v___x_3796_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_dec(v_____x_3790_);
lean_dec(v_toBind_3789_);
lean_dec_ref(v_binderType_3788_);
lean_dec(v_fieldVal_x3f_3787_);
lean_dec(v_inst_3786_);
lean_dec_ref(v_inst_3785_);
lean_dec_ref(v_body_3784_);
lean_dec(v_binderName_3783_);
lean_dec(v_usedFields_3782_);
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_apply_2(v_toPure_3781_, lean_box(0), v___x_3797_);
return v___x_3798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3802_, lean_object* v_inst_3803_, lean_object* v_fieldVal_x3f_3804_, lean_object* v_usedFields_3805_, lean_object* v_e_3806_){
_start:
{
lean_object* v_toApplicative_3807_; lean_object* v_toBind_3808_; lean_object* v_toPure_3809_; 
v_toApplicative_3807_ = lean_ctor_get(v_inst_3802_, 0);
v_toBind_3808_ = lean_ctor_get(v_inst_3802_, 1);
v_toPure_3809_ = lean_ctor_get(v_toApplicative_3807_, 1);
lean_inc(v_toPure_3809_);
if (lean_obj_tag(v_e_3806_) == 6)
{
lean_object* v_binderName_3814_; lean_object* v_binderType_3815_; lean_object* v_body_3816_; lean_object* v___f_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_inc(v_toBind_3808_);
v_binderName_3814_ = lean_ctor_get(v_e_3806_, 0);
lean_inc(v_binderName_3814_);
v_binderType_3815_ = lean_ctor_get(v_e_3806_, 1);
lean_inc_ref(v_binderType_3815_);
v_body_3816_ = lean_ctor_get(v_e_3806_, 2);
lean_inc_ref(v_body_3816_);
lean_dec_ref(v_e_3806_);
lean_inc(v_toBind_3808_);
lean_inc(v_fieldVal_x3f_3804_);
lean_inc(v_binderName_3814_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3817_, 0, v_toPure_3809_);
lean_closure_set(v___f_3817_, 1, v_usedFields_3805_);
lean_closure_set(v___f_3817_, 2, v_binderName_3814_);
lean_closure_set(v___f_3817_, 3, v_body_3816_);
lean_closure_set(v___f_3817_, 4, v_inst_3802_);
lean_closure_set(v___f_3817_, 5, v_inst_3803_);
lean_closure_set(v___f_3817_, 6, v_fieldVal_x3f_3804_);
lean_closure_set(v___f_3817_, 7, v_binderType_3815_);
lean_closure_set(v___f_3817_, 8, v_toBind_3808_);
v___x_3818_ = lean_apply_1(v_fieldVal_x3f_3804_, v_binderName_3814_);
v___x_3819_ = lean_apply_4(v_toBind_3808_, lean_box(0), lean_box(0), v___x_3818_, v___f_3817_);
return v___x_3819_;
}
else
{
lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v_fieldVal_x3f_3804_);
lean_dec(v_inst_3803_);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_inst_3802_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3837_ = lean_ctor_get(v_inst_3802_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_inst_3802_, 0);
lean_dec(v_unused_3838_);
v___x_3821_ = v_inst_3802_;
v_isShared_3822_ = v_isSharedCheck_3836_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v_inst_3802_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3836_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; uint8_t v___x_3824_; 
lean_inc_ref(v_e_3806_);
v___x_3823_ = l_Lean_Expr_cleanupAnnotations(v_e_3806_);
v___x_3824_ = l_Lean_Expr_isApp(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_dec_ref(v___x_3823_);
lean_del_object(v___x_3821_);
goto v___jp_3810_;
}
else
{
lean_object* v_arg_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_arg_3825_ = lean_ctor_get(v___x_3823_, 1);
lean_inc_ref(v_arg_3825_);
v___x_3826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3823_);
v___x_3827_ = l_Lean_Expr_isApp(v___x_3826_);
if (v___x_3827_ == 0)
{
lean_dec_ref(v___x_3826_);
lean_dec_ref(v_arg_3825_);
lean_del_object(v___x_3821_);
goto v___jp_3810_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3826_);
v___x_3829_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3830_ = l_Lean_Expr_isConstOf(v___x_3828_, v___x_3829_);
lean_dec_ref(v___x_3828_);
if (v___x_3830_ == 0)
{
lean_dec_ref(v_arg_3825_);
lean_del_object(v___x_3821_);
goto v___jp_3810_;
}
else
{
lean_object* v___x_3832_; 
lean_dec_ref(v_e_3806_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v_arg_3825_);
lean_ctor_set(v___x_3821_, 0, v_usedFields_3805_);
v___x_3832_ = v___x_3821_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_usedFields_3805_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_arg_3825_);
v___x_3832_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
v___x_3834_ = lean_apply_2(v_toPure_3809_, lean_box(0), v___x_3833_);
return v___x_3834_;
}
}
}
}
}
}
v___jp_3810_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_usedFields_3805_);
lean_ctor_set(v___x_3811_, 1, v_e_3806_);
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
v___x_3813_ = lean_apply_2(v_toPure_3809_, lean_box(0), v___x_3812_);
return v___x_3813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3839_, lean_object* v_usedFields_3840_, lean_object* v_binderName_3841_, lean_object* v_body_3842_, lean_object* v_val_3843_, lean_object* v_inst_3844_, lean_object* v_inst_3845_, lean_object* v_fieldVal_x3f_3846_, uint8_t v_____do__lift_3847_){
_start:
{
if (v_____do__lift_3847_ == 0)
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec(v_fieldVal_x3f_3846_);
lean_dec(v_inst_3845_);
lean_dec_ref(v_inst_3844_);
lean_dec(v_binderName_3841_);
lean_dec(v_usedFields_3840_);
v___x_3848_ = lean_box(0);
v___x_3849_ = lean_apply_2(v_toPure_3839_, lean_box(0), v___x_3848_);
return v___x_3849_;
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_dec(v_toPure_3839_);
v___x_3850_ = l_Lean_NameSet_insert(v_usedFields_3840_, v_binderName_3841_);
v___x_3851_ = lean_expr_instantiate1(v_body_3842_, v_val_3843_);
v___x_3852_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3844_, v_inst_3845_, v_fieldVal_x3f_3846_, v___x_3850_, v___x_3851_);
return v___x_3852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3853_, lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_fieldVal_x3f_3856_, lean_object* v_usedFields_3857_, lean_object* v_e_3858_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3854_, v_inst_3855_, v_fieldVal_x3f_3856_, v_usedFields_3857_, v_e_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3860_, lean_object* v_inst_3861_, lean_object* v_fieldVal_x3f_3862_, lean_object* v_toPure_3863_, lean_object* v_____s_3864_){
_start:
{
lean_object* v_fst_3865_; 
v_fst_3865_ = lean_ctor_get(v_____s_3864_, 0);
if (lean_obj_tag(v_fst_3865_) == 0)
{
lean_object* v_snd_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_dec(v_toPure_3863_);
v_snd_3866_ = lean_ctor_get(v_____s_3864_, 1);
lean_inc(v_snd_3866_);
lean_dec_ref(v_____s_3864_);
v___x_3867_ = l_Lean_NameSet_empty;
v___x_3868_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3860_, v_inst_3861_, v_fieldVal_x3f_3862_, v___x_3867_, v_snd_3866_);
return v___x_3868_;
}
else
{
lean_object* v_val_3869_; lean_object* v___x_3870_; 
lean_inc_ref(v_fst_3865_);
lean_dec_ref(v_____s_3864_);
lean_dec(v_fieldVal_x3f_3862_);
lean_dec(v_inst_3861_);
lean_dec_ref(v_inst_3860_);
v_val_3869_ = lean_ctor_get(v_fst_3865_, 0);
lean_inc(v_val_3869_);
lean_dec_ref(v_fst_3865_);
v___x_3870_ = lean_apply_2(v_toPure_3863_, lean_box(0), v_val_3869_);
return v___x_3870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3871_, lean_object* v_a_3872_, lean_object* v___x_3873_, lean_object* v_toPure_3874_, lean_object* v_____r_3875_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3876_ = lean_expr_instantiate1(v_body_3871_, v_a_3872_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3873_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
v___x_3879_ = lean_apply_2(v_toPure_3874_, lean_box(0), v___x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3880_, lean_object* v_a_3881_, lean_object* v___x_3882_, lean_object* v_toPure_3883_, lean_object* v_____r_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3880_, v_a_3881_, v___x_3882_, v_toPure_3883_, v_____r_3884_);
lean_dec_ref(v_a_3881_);
lean_dec_ref(v_body_3880_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3888_, lean_object* v_toPure_3889_, lean_object* v___f_3890_, uint8_t v_____do__lift_3891_){
_start:
{
if (v_____do__lift_3891_ == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v___f_3890_);
v___x_3892_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v_snd_3888_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v___x_3895_ = lean_apply_2(v_toPure_3889_, lean_box(0), v___x_3894_);
return v___x_3895_;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec(v_toPure_3889_);
lean_dec(v_snd_3888_);
v___x_3896_ = lean_box(0);
v___x_3897_ = lean_apply_1(v___f_3890_, v___x_3896_);
return v___x_3897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3898_, lean_object* v_toPure_3899_, lean_object* v___f_3900_, lean_object* v_____do__lift_3901_){
_start:
{
uint8_t v_____do__lift_850__boxed_3902_; lean_object* v_res_3903_; 
v_____do__lift_850__boxed_3902_ = lean_unbox(v_____do__lift_3901_);
v_res_3903_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3898_, v_toPure_3899_, v___f_3900_, v_____do__lift_850__boxed_3902_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3904_, lean_object* v_inst_3905_, lean_object* v_toBind_3906_, lean_object* v___f_3907_, lean_object* v_____do__lift_3908_){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3909_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3909_, 0, v_____do__lift_3908_);
lean_closure_set(v___x_3909_, 1, v_binderType_3904_);
v___x_3910_ = lean_apply_2(v_inst_3905_, lean_box(0), v___x_3909_);
v___x_3911_ = lean_apply_4(v_toBind_3906_, lean_box(0), lean_box(0), v___x_3910_, v___f_3907_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3912_, lean_object* v_toPure_3913_, lean_object* v_levels_x3f_3914_, uint8_t v___x_3915_, lean_object* v_inst_3916_, lean_object* v_toBind_3917_, lean_object* v_a_3918_, lean_object* v_x_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_snd_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3942_; 
v_snd_3921_ = lean_ctor_get(v___y_3920_, 1);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___y_3920_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v___y_3920_, 0);
lean_dec(v_unused_3943_);
v___x_3923_ = v___y_3920_;
v_isShared_3924_ = v_isSharedCheck_3942_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_snd_3921_);
lean_dec(v___y_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3942_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
if (lean_obj_tag(v_snd_3921_) == 6)
{
lean_object* v_binderType_3925_; lean_object* v_body_3926_; lean_object* v___f_3927_; 
lean_del_object(v___x_3923_);
v_binderType_3925_ = lean_ctor_get(v_snd_3921_, 1);
lean_inc_ref(v_binderType_3925_);
v_body_3926_ = lean_ctor_get(v_snd_3921_, 2);
lean_inc(v_toPure_3913_);
lean_inc(v___x_3912_);
lean_inc_ref(v_a_3918_);
lean_inc_ref(v_body_3926_);
v___f_3927_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3927_, 0, v_body_3926_);
lean_closure_set(v___f_3927_, 1, v_a_3918_);
lean_closure_set(v___f_3927_, 2, v___x_3912_);
lean_closure_set(v___f_3927_, 3, v_toPure_3913_);
if (lean_obj_tag(v_levels_x3f_3914_) == 0)
{
if (v___x_3915_ == 0)
{
lean_inc_ref(v_body_3926_);
lean_dec_ref(v___f_3927_);
lean_dec_ref(v_binderType_3925_);
lean_dec_ref(v_snd_3921_);
lean_dec(v_toBind_3917_);
lean_dec(v_inst_3916_);
goto v___jp_3928_;
}
else
{
lean_object* v___f_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec(v___x_3912_);
v___f_3931_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3931_, 0, v_snd_3921_);
lean_closure_set(v___f_3931_, 1, v_toPure_3913_);
lean_closure_set(v___f_3931_, 2, v___f_3927_);
lean_inc(v_toBind_3917_);
lean_inc(v_inst_3916_);
v___f_3932_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3932_, 0, v_binderType_3925_);
lean_closure_set(v___f_3932_, 1, v_inst_3916_);
lean_closure_set(v___f_3932_, 2, v_toBind_3917_);
lean_closure_set(v___f_3932_, 3, v___f_3931_);
v___x_3933_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3933_, 0, v_a_3918_);
v___x_3934_ = lean_apply_2(v_inst_3916_, lean_box(0), v___x_3933_);
v___x_3935_ = lean_apply_4(v_toBind_3917_, lean_box(0), lean_box(0), v___x_3934_, v___f_3932_);
return v___x_3935_;
}
}
else
{
lean_inc_ref(v_body_3926_);
lean_dec_ref(v___f_3927_);
lean_dec_ref(v_binderType_3925_);
lean_dec_ref(v_snd_3921_);
lean_dec(v_toBind_3917_);
lean_dec(v_inst_3916_);
goto v___jp_3928_;
}
v___jp_3928_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3926_, v_a_3918_, v___x_3912_, v_toPure_3913_, v___x_3929_);
lean_dec_ref(v_a_3918_);
lean_dec_ref(v_body_3926_);
return v___x_3930_;
}
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
lean_dec_ref(v_a_3918_);
lean_dec(v_toBind_3917_);
lean_dec(v_inst_3916_);
lean_dec(v___x_3912_);
v___x_3936_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3936_);
v___x_3938_ = v___x_3923_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_snd_3921_);
v___x_3938_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
v___x_3940_ = lean_apply_2(v_toPure_3913_, lean_box(0), v___x_3939_);
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3944_, lean_object* v_toPure_3945_, lean_object* v_levels_x3f_3946_, lean_object* v___x_3947_, lean_object* v_inst_3948_, lean_object* v_toBind_3949_, lean_object* v_a_3950_, lean_object* v_x_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v___x_886__boxed_3953_; lean_object* v_res_3954_; 
v___x_886__boxed_3953_ = lean_unbox(v___x_3947_);
v_res_3954_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3944_, v_toPure_3945_, v_levels_x3f_3946_, v___x_886__boxed_3953_, v_inst_3948_, v_toBind_3949_, v_a_3950_, v_x_3951_, v___y_3952_);
lean_dec(v_levels_x3f_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3955_, lean_object* v_levels_x3f_3956_, uint8_t v___x_3957_, lean_object* v_inst_3958_, lean_object* v_toBind_3959_, lean_object* v_params_3960_, lean_object* v_inst_3961_, lean_object* v___f_3962_, lean_object* v_val_3963_){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___f_3966_; lean_object* v___x_3967_; size_t v_sz_3968_; size_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3964_ = lean_box(0);
v___x_3965_ = lean_box(v___x_3957_);
lean_inc(v_toBind_3959_);
v___f_3966_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_3966_, 0, v___x_3964_);
lean_closure_set(v___f_3966_, 1, v_toPure_3955_);
lean_closure_set(v___f_3966_, 2, v_levels_x3f_3956_);
lean_closure_set(v___f_3966_, 3, v___x_3965_);
lean_closure_set(v___f_3966_, 4, v_inst_3958_);
lean_closure_set(v___f_3966_, 5, v_toBind_3959_);
v___x_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3964_);
lean_ctor_set(v___x_3967_, 1, v_val_3963_);
v_sz_3968_ = lean_array_size(v_params_3960_);
v___x_3969_ = ((size_t)0ULL);
v___x_3970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3961_, v_params_3960_, v___f_3966_, v_sz_3968_, v___x_3969_, v___x_3967_);
v___x_3971_ = lean_apply_4(v_toBind_3959_, lean_box(0), lean_box(0), v___x_3970_, v___f_3962_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(lean_object* v_toPure_3972_, lean_object* v_levels_x3f_3973_, lean_object* v___x_3974_, lean_object* v_inst_3975_, lean_object* v_toBind_3976_, lean_object* v_params_3977_, lean_object* v_inst_3978_, lean_object* v___f_3979_, lean_object* v_val_3980_){
_start:
{
uint8_t v___x_948__boxed_3981_; lean_object* v_res_3982_; 
v___x_948__boxed_3981_ = lean_unbox(v___x_3974_);
v_res_3982_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(v_toPure_3972_, v_levels_x3f_3973_, v___x_948__boxed_3981_, v_inst_3975_, v_toBind_3976_, v_params_3977_, v_inst_3978_, v___f_3979_, v_val_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3983_, lean_object* v_us_3984_, uint8_t v___x_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3983_, v_us_3984_, v___x_3985_, v___y_3988_, v___y_3989_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3992_, lean_object* v_us_3993_, lean_object* v___x_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v___x_974__boxed_4000_; lean_object* v_res_4001_; 
v___x_974__boxed_4000_ = lean_unbox(v___x_3994_);
v_res_4001_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3992_, v_us_3993_, v___x_974__boxed_4000_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v_cinfo_3992_);
return v_res_4001_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4005_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4006_ = lean_unsigned_to_nat(2u);
v___x_4007_ = lean_unsigned_to_nat(202u);
v___x_4008_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4009_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4010_ = l_mkPanicMessageWithDecl(v___x_4009_, v___x_4008_, v___x_4007_, v___x_4006_, v___x_4005_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4011_, lean_object* v_inst_4012_, lean_object* v_toPure_4013_, lean_object* v_levels_x3f_4014_, lean_object* v_inst_4015_, lean_object* v_toBind_4016_, lean_object* v_params_4017_, lean_object* v___f_4018_, lean_object* v_us_4019_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4020_ = l_List_lengthTR___redArg(v_us_4019_);
v___x_4021_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4011_);
v___x_4022_ = l_List_lengthTR___redArg(v___x_4021_);
lean_dec(v___x_4021_);
v___x_4023_ = lean_nat_dec_eq(v___x_4020_, v___x_4022_);
lean_dec(v___x_4022_);
lean_dec(v___x_4020_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
lean_dec(v_us_4019_);
lean_dec(v___f_4018_);
lean_dec_ref(v_params_4017_);
lean_dec(v_toBind_4016_);
lean_dec(v_inst_4015_);
lean_dec(v_levels_x3f_4014_);
lean_dec(v_toPure_4013_);
lean_dec_ref(v_cinfo_4011_);
v___x_4024_ = lean_box(0);
v___x_4025_ = l_instInhabitedOfMonad___redArg(v_inst_4012_, v___x_4024_);
v___x_4026_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4027_ = l_panic___redArg(v___x_4025_, v___x_4026_);
return v___x_4027_;
}
else
{
lean_object* v___x_4028_; lean_object* v___f_4029_; uint8_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___f_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4028_ = lean_box(v___x_4023_);
lean_inc(v_toBind_4016_);
lean_inc(v_inst_4015_);
v___f_4029_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_4029_, 0, v_toPure_4013_);
lean_closure_set(v___f_4029_, 1, v_levels_x3f_4014_);
lean_closure_set(v___f_4029_, 2, v___x_4028_);
lean_closure_set(v___f_4029_, 3, v_inst_4015_);
lean_closure_set(v___f_4029_, 4, v_toBind_4016_);
lean_closure_set(v___f_4029_, 5, v_params_4017_);
lean_closure_set(v___f_4029_, 6, v_inst_4012_);
lean_closure_set(v___f_4029_, 7, v___f_4018_);
v___x_4030_ = 0;
v___x_4031_ = lean_box(v___x_4030_);
v___f_4032_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4032_, 0, v_cinfo_4011_);
lean_closure_set(v___f_4032_, 1, v_us_4019_);
lean_closure_set(v___f_4032_, 2, v___x_4031_);
v___x_4033_ = lean_apply_2(v_inst_4015_, lean_box(0), v___f_4032_);
v___x_4034_ = lean_apply_4(v_toBind_4016_, lean_box(0), lean_box(0), v___x_4033_, v___f_4029_);
return v___x_4034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v_inst_4035_, lean_object* v_toPure_4036_, lean_object* v_levels_x3f_4037_, lean_object* v_inst_4038_, lean_object* v_toBind_4039_, lean_object* v_params_4040_, lean_object* v___f_4041_, lean_object* v_cinfo_4042_){
_start:
{
lean_object* v___f_4043_; 
lean_inc(v_toBind_4039_);
lean_inc(v_inst_4038_);
lean_inc(v_levels_x3f_4037_);
lean_inc(v_toPure_4036_);
lean_inc_ref(v_cinfo_4042_);
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7), 9, 8);
lean_closure_set(v___f_4043_, 0, v_cinfo_4042_);
lean_closure_set(v___f_4043_, 1, v_inst_4035_);
lean_closure_set(v___f_4043_, 2, v_toPure_4036_);
lean_closure_set(v___f_4043_, 3, v_levels_x3f_4037_);
lean_closure_set(v___f_4043_, 4, v_inst_4038_);
lean_closure_set(v___f_4043_, 5, v_toBind_4039_);
lean_closure_set(v___f_4043_, 6, v_params_4040_);
lean_closure_set(v___f_4043_, 7, v___f_4041_);
if (lean_obj_tag(v_levels_x3f_4037_) == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_dec(v_toPure_4036_);
v___x_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4044_, 0, v_cinfo_4042_);
v___x_4045_ = lean_apply_2(v_inst_4038_, lean_box(0), v___x_4044_);
v___x_4046_ = lean_apply_4(v_toBind_4039_, lean_box(0), lean_box(0), v___x_4045_, v___f_4043_);
return v___x_4046_;
}
else
{
lean_object* v_val_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec_ref(v_cinfo_4042_);
lean_dec(v_inst_4038_);
v_val_4047_ = lean_ctor_get(v_levels_x3f_4037_, 0);
lean_inc(v_val_4047_);
lean_dec_ref(v_levels_x3f_4037_);
v___x_4048_ = lean_apply_2(v_toPure_4036_, lean_box(0), v_val_4047_);
v___x_4049_ = lean_apply_4(v_toBind_4039_, lean_box(0), lean_box(0), v___x_4048_, v___f_4043_);
return v___x_4049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_defaultFn_4054_, lean_object* v_levels_x3f_4055_, lean_object* v_params_4056_, lean_object* v_fieldVal_x3f_4057_){
_start:
{
lean_object* v_toApplicative_4058_; lean_object* v_toBind_4059_; lean_object* v_toPure_4060_; lean_object* v___x_4061_; lean_object* v___f_4062_; lean_object* v___f_4063_; lean_object* v___x_4064_; 
v_toApplicative_4058_ = lean_ctor_get(v_inst_4050_, 0);
v_toBind_4059_ = lean_ctor_get(v_inst_4050_, 1);
lean_inc(v_toBind_4059_);
v_toPure_4060_ = lean_ctor_get(v_toApplicative_4058_, 1);
lean_inc(v_toPure_4060_);
lean_inc_ref(v_inst_4050_);
v___x_4061_ = l_Lean_getConstInfo___redArg(v_inst_4050_, v_inst_4051_, v_inst_4052_, v_defaultFn_4054_);
lean_inc(v_toPure_4060_);
lean_inc(v_inst_4053_);
lean_inc_ref(v_inst_4050_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4062_, 0, v_inst_4050_);
lean_closure_set(v___f_4062_, 1, v_inst_4053_);
lean_closure_set(v___f_4062_, 2, v_fieldVal_x3f_4057_);
lean_closure_set(v___f_4062_, 3, v_toPure_4060_);
lean_inc(v_toBind_4059_);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 8, 7);
lean_closure_set(v___f_4063_, 0, v_inst_4050_);
lean_closure_set(v___f_4063_, 1, v_toPure_4060_);
lean_closure_set(v___f_4063_, 2, v_levels_x3f_4055_);
lean_closure_set(v___f_4063_, 3, v_inst_4053_);
lean_closure_set(v___f_4063_, 4, v_toBind_4059_);
lean_closure_set(v___f_4063_, 5, v_params_4056_);
lean_closure_set(v___f_4063_, 6, v___f_4062_);
v___x_4064_ = lean_apply_4(v_toBind_4059_, lean_box(0), lean_box(0), v___x_4061_, v___f_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4065_, lean_object* v_inst_4066_, lean_object* v_inst_4067_, lean_object* v_inst_4068_, lean_object* v_inst_4069_, lean_object* v_inst_4070_, lean_object* v_defaultFn_4071_, lean_object* v_levels_x3f_4072_, lean_object* v_params_4073_, lean_object* v_fieldVal_x3f_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4066_, v_inst_4067_, v_inst_4068_, v_inst_4069_, v_defaultFn_4071_, v_levels_x3f_4072_, v_params_4073_, v_fieldVal_x3f_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4076_, lean_object* v_inst_4077_, lean_object* v_inst_4078_, lean_object* v_inst_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_defaultFn_4082_, lean_object* v_levels_x3f_4083_, lean_object* v_params_4084_, lean_object* v_fieldVal_x3f_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4076_, v_inst_4077_, v_inst_4078_, v_inst_4079_, v_inst_4080_, v_inst_4081_, v_defaultFn_4082_, v_levels_x3f_4083_, v_params_4084_, v_fieldVal_x3f_4085_);
lean_dec_ref(v_inst_4081_);
return v_res_4086_;
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
