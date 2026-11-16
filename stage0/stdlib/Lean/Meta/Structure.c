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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to generate projection `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` for the 'Prop'-valued type `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`, field must be a proof, but it has type"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`, too many structure parameter overrides"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`, not enough constructor fields"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(lean_object* v_name_110_, lean_object* v_levelParams_111_, lean_object* v_type_112_, lean_object* v_value_113_, lean_object* v_hints_114_, lean_object* v___y_115_){
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
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg___boxed(lean_object* v_name_131_, lean_object* v_levelParams_132_, lean_object* v_type_133_, lean_object* v_value_134_, lean_object* v_hints_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(v_name_131_, v_levelParams_132_, v_type_133_, v_value_134_, v_hints_135_, v___y_136_);
lean_dec(v___y_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5(lean_object* v_name_139_, lean_object* v_levelParams_140_, lean_object* v_type_141_, lean_object* v_value_142_, lean_object* v_hints_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(v_name_139_, v_levelParams_140_, v_type_141_, v_value_142_, v_hints_143_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___boxed(lean_object* v_name_150_, lean_object* v_levelParams_151_, lean_object* v_type_152_, lean_object* v_value_153_, lean_object* v_hints_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5(v_name_150_, v_levelParams_151_, v_type_152_, v_value_153_, v_hints_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(lean_object* v_k_161_, lean_object* v_b_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(lean_object* v_k_169_, lean_object* v_b_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_169_, v_b_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(lean_object* v_name_177_, uint8_t v_bi_178_, lean_object* v_type_179_, lean_object* v_k_180_, uint8_t v_kind_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed), 7, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(lean_object* v_name_205_, lean_object* v_bi_206_, lean_object* v_type_207_, lean_object* v_k_208_, lean_object* v_kind_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v_bi_boxed_215_; uint8_t v_kind_boxed_216_; lean_object* v_res_217_; 
v_bi_boxed_215_ = lean_unbox(v_bi_206_);
v_kind_boxed_216_ = lean_unbox(v_kind_209_);
v_res_217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(v_name_205_, v_bi_boxed_215_, v_type_207_, v_k_208_, v_kind_boxed_216_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10(lean_object* v_00_u03b1_218_, lean_object* v_name_219_, uint8_t v_bi_220_, lean_object* v_type_221_, lean_object* v_k_222_, uint8_t v_kind_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(v_name_219_, v_bi_220_, v_type_221_, v_k_222_, v_kind_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___boxed(lean_object* v_00_u03b1_230_, lean_object* v_name_231_, lean_object* v_bi_232_, lean_object* v_type_233_, lean_object* v_k_234_, lean_object* v_kind_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
uint8_t v_bi_boxed_241_; uint8_t v_kind_boxed_242_; lean_object* v_res_243_; 
v_bi_boxed_241_ = lean_unbox(v_bi_232_);
v_kind_boxed_242_ = lean_unbox(v_kind_235_);
v_res_243_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10(v_00_u03b1_230_, v_name_231_, v_bi_boxed_241_, v_type_233_, v_k_234_, v_kind_boxed_242_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0(lean_object* v_k_244_, lean_object* v_b_245_, lean_object* v_c_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0___boxed(lean_object* v_k_253_, lean_object* v_b_254_, lean_object* v_c_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0(v_k_253_, v_b_254_, v_c_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(lean_object* v_type_262_, lean_object* v_maxFVars_x3f_263_, lean_object* v_k_264_, uint8_t v_cleanupAnnotations_265_, uint8_t v_whnfType_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; 
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(lean_object* v_type_290_, lean_object* v_maxFVars_x3f_291_, lean_object* v_k_292_, lean_object* v_cleanupAnnotations_293_, lean_object* v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_300_; uint8_t v_whnfType_boxed_301_; lean_object* v_res_302_; 
v_cleanupAnnotations_boxed_300_ = lean_unbox(v_cleanupAnnotations_293_);
v_whnfType_boxed_301_ = lean_unbox(v_whnfType_294_);
v_res_302_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(v_type_290_, v_maxFVars_x3f_291_, v_k_292_, v_cleanupAnnotations_boxed_300_, v_whnfType_boxed_301_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11(lean_object* v_00_u03b1_303_, lean_object* v_type_304_, lean_object* v_maxFVars_x3f_305_, lean_object* v_k_306_, uint8_t v_cleanupAnnotations_307_, uint8_t v_whnfType_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(v_type_304_, v_maxFVars_x3f_305_, v_k_306_, v_cleanupAnnotations_307_, v_whnfType_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___boxed(lean_object* v_00_u03b1_315_, lean_object* v_type_316_, lean_object* v_maxFVars_x3f_317_, lean_object* v_k_318_, lean_object* v_cleanupAnnotations_319_, lean_object* v_whnfType_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_326_; uint8_t v_whnfType_boxed_327_; lean_object* v_res_328_; 
v_cleanupAnnotations_boxed_326_ = lean_unbox(v_cleanupAnnotations_319_);
v_whnfType_boxed_327_ = lean_unbox(v_whnfType_320_);
v_res_328_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11(v_00_u03b1_315_, v_type_316_, v_maxFVars_x3f_317_, v_k_318_, v_cleanupAnnotations_boxed_326_, v_whnfType_boxed_327_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(lean_object* v_lctx_329_, lean_object* v_localInsts_330_, lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg___boxed(lean_object* v_lctx_354_, lean_object* v_localInsts_355_, lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(v_lctx_354_, v_localInsts_355_, v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12(lean_object* v_00_u03b1_363_, lean_object* v_lctx_364_, lean_object* v_localInsts_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(v_lctx_364_, v_localInsts_365_, v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___boxed(lean_object* v_00_u03b1_373_, lean_object* v_lctx_374_, lean_object* v_localInsts_375_, lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12(v_00_u03b1_373_, v_lctx_374_, v_localInsts_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(uint8_t v_instImplicit_383_, lean_object* v_as_384_, size_t v_sz_385_, size_t v_i_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_a_393_; uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_386_, v_sz_385_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_387_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_a_399_ = lean_array_uget_borrowed(v_as_384_, v_i_386_);
v___x_400_ = l_Lean_Expr_fvarId_x21(v_a_399_);
lean_inc(v___x_400_);
v___x_401_ = l_Lean_FVarId_getDecl___redArg(v___x_400_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; uint8_t v___x_403_; uint8_t v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_LocalDecl_binderInfo(v_a_402_);
v___x_404_ = l_Lean_BinderInfo_isInstImplicit(v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = l_Lean_LocalDecl_type(v_a_402_);
lean_dec(v_a_402_);
v___x_409_ = l_Lean_Expr_isOutParam(v___x_408_);
lean_dec_ref(v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; lean_object* v___x_411_; 
v___x_410_ = 0;
v___x_411_ = l_Lean_LocalContext_setBinderInfo(v_b_387_, v___x_400_, v___x_410_);
v_a_393_ = v___x_411_;
goto v___jp_392_;
}
else
{
goto v___jp_405_;
}
}
else
{
lean_dec(v_a_402_);
goto v___jp_405_;
}
v___jp_405_:
{
if (v___x_404_ == 0)
{
lean_dec(v___x_400_);
v_a_393_ = v_b_387_;
goto v___jp_392_;
}
else
{
if (v_instImplicit_383_ == 0)
{
lean_dec(v___x_400_);
v_a_393_ = v_b_387_;
goto v___jp_392_;
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; 
v___x_406_ = 1;
v___x_407_ = l_Lean_LocalContext_setBinderInfo(v_b_387_, v___x_400_, v___x_406_);
v_a_393_ = v___x_407_;
goto v___jp_392_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v___x_400_);
lean_dec_ref(v_b_387_);
v_a_412_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_401_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_401_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
v___jp_392_:
{
size_t v___x_394_; size_t v___x_395_; 
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_386_, v___x_394_);
v_i_386_ = v___x_395_;
v_b_387_ = v_a_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(lean_object* v_instImplicit_420_, lean_object* v_as_421_, lean_object* v_sz_422_, lean_object* v_i_423_, lean_object* v_b_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v_instImplicit_boxed_429_; size_t v_sz_boxed_430_; size_t v_i_boxed_431_; lean_object* v_res_432_; 
v_instImplicit_boxed_429_ = lean_unbox(v_instImplicit_420_);
v_sz_boxed_430_ = lean_unbox_usize(v_sz_422_);
lean_dec(v_sz_422_);
v_i_boxed_431_ = lean_unbox_usize(v_i_423_);
lean_dec(v_i_423_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_429_, v_as_421_, v_sz_boxed_430_, v_i_boxed_431_, v_b_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v_as_421_);
return v_res_432_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_433_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg(){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__1);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___boxed(lean_object* v___dummy_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg();
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(lean_object* v___y_440_, uint8_t v_isExporting_441_, lean_object* v___x_442_, lean_object* v___y_443_, lean_object* v___x_444_, lean_object* v_a_x3f_445_){
_start:
{
lean_object* v___x_447_; lean_object* v_env_448_; lean_object* v_nextMacroScope_449_; lean_object* v_ngen_450_; lean_object* v_auxDeclNGen_451_; lean_object* v_traceState_452_; lean_object* v_recordedDeps_453_; lean_object* v_messages_454_; lean_object* v_infoState_455_; lean_object* v_snapshotTasks_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_481_; 
v___x_447_ = lean_st_ref_take(v___y_440_);
v_env_448_ = lean_ctor_get(v___x_447_, 0);
v_nextMacroScope_449_ = lean_ctor_get(v___x_447_, 1);
v_ngen_450_ = lean_ctor_get(v___x_447_, 2);
v_auxDeclNGen_451_ = lean_ctor_get(v___x_447_, 3);
v_traceState_452_ = lean_ctor_get(v___x_447_, 4);
v_recordedDeps_453_ = lean_ctor_get(v___x_447_, 6);
v_messages_454_ = lean_ctor_get(v___x_447_, 7);
v_infoState_455_ = lean_ctor_get(v___x_447_, 8);
v_snapshotTasks_456_ = lean_ctor_get(v___x_447_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v___x_447_, 5);
lean_dec(v_unused_482_);
v___x_458_ = v___x_447_;
v_isShared_459_ = v_isSharedCheck_481_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snapshotTasks_456_);
lean_inc(v_infoState_455_);
lean_inc(v_messages_454_);
lean_inc(v_recordedDeps_453_);
lean_inc(v_traceState_452_);
lean_inc(v_auxDeclNGen_451_);
lean_inc(v_ngen_450_);
lean_inc(v_nextMacroScope_449_);
lean_inc(v_env_448_);
lean_dec(v___x_447_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_481_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_Environment_setExporting(v_env_448_, v_isExporting_441_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 5, v___x_442_);
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_nextMacroScope_449_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_ngen_450_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_auxDeclNGen_451_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_traceState_452_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_recordedDeps_453_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_messages_454_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v_infoState_455_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_snapshotTasks_456_);
v___x_462_ = v_reuseFailAlloc_480_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_mctx_465_; lean_object* v_zetaDeltaFVarIds_466_; lean_object* v_postponed_467_; lean_object* v_diag_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_478_; 
v___x_463_ = lean_st_ref_put(v___y_440_, v___x_462_);
v___x_464_ = lean_st_ref_take(v___y_443_);
v_mctx_465_ = lean_ctor_get(v___x_464_, 0);
v_zetaDeltaFVarIds_466_ = lean_ctor_get(v___x_464_, 2);
v_postponed_467_ = lean_ctor_get(v___x_464_, 3);
v_diag_468_ = lean_ctor_get(v___x_464_, 4);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v___x_464_, 1);
lean_dec(v_unused_479_);
v___x_470_ = v___x_464_;
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_diag_468_);
lean_inc(v_postponed_467_);
lean_inc(v_zetaDeltaFVarIds_466_);
lean_inc(v_mctx_465_);
lean_dec(v___x_464_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_478_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_444_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_mctx_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_zetaDeltaFVarIds_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_postponed_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_diag_468_);
v___x_474_ = v_reuseFailAlloc_477_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_st_ref_put(v___y_443_, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_472_);
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0___boxed(lean_object* v___y_483_, lean_object* v_isExporting_484_, lean_object* v___x_485_, lean_object* v___y_486_, lean_object* v___x_487_, lean_object* v_a_x3f_488_, lean_object* v___y_489_){
_start:
{
uint8_t v_isExporting_boxed_490_; lean_object* v_res_491_; 
v_isExporting_boxed_490_ = lean_unbox(v_isExporting_484_);
v_res_491_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(v___y_483_, v_isExporting_boxed_490_, v___x_485_, v___y_486_, v___x_487_, v_a_x3f_488_);
lean_dec(v_a_x3f_488_);
lean_dec(v___y_486_);
lean_dec(v___y_483_);
return v_res_491_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg();
return v___x_496_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0);
v___x_501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
lean_ctor_set(v___x_501_, 2, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_502_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__4);
v___x_503_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3);
v___x_504_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0);
v___x_505_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
v___x_506_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
lean_ctor_set(v___x_506_, 2, v___x_503_);
lean_ctor_set(v___x_506_, 3, v___x_504_);
lean_ctor_set(v___x_506_, 4, v___x_504_);
lean_ctor_set(v___x_506_, 5, v___x_504_);
lean_ctor_set(v___x_506_, 6, v___x_504_);
lean_ctor_set(v___x_506_, 7, v___x_502_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(lean_object* v_x_507_, uint8_t v_isExporting_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v___x_516_; uint8_t v_isModule_517_; 
v___x_514_ = lean_st_ref_get(v___y_512_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_515_);
lean_dec(v___x_514_);
v___x_516_ = l_Lean_Environment_header(v_env_515_);
v_isModule_517_ = lean_ctor_get_uint8(v___x_516_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_516_);
if (v_isModule_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v_env_515_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
v___x_518_ = lean_apply_5(v_x_507_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, lean_box(0));
return v___x_518_;
}
else
{
uint8_t v_isExporting_519_; 
v_isExporting_519_ = lean_ctor_get_uint8(v_env_515_, sizeof(void*)*13);
lean_dec_ref(v_env_515_);
if (v_isExporting_508_ == 0)
{
if (v_isExporting_519_ == 0)
{
lean_object* v___x_586_; 
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
v___x_586_ = lean_apply_5(v_x_507_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, lean_box(0));
return v___x_586_;
}
else
{
goto v___jp_520_;
}
}
else
{
if (v_isExporting_519_ == 0)
{
goto v___jp_520_;
}
else
{
lean_object* v___x_587_; 
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
v___x_587_ = lean_apply_5(v_x_507_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, lean_box(0));
return v___x_587_;
}
}
v___jp_520_:
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_traceState_526_; lean_object* v_recordedDeps_527_; lean_object* v_messages_528_; lean_object* v_infoState_529_; lean_object* v_snapshotTasks_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_584_; 
v___x_521_ = lean_st_ref_take(v___y_512_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_521_, 1);
v_ngen_524_ = lean_ctor_get(v___x_521_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_521_, 3);
v_traceState_526_ = lean_ctor_get(v___x_521_, 4);
v_recordedDeps_527_ = lean_ctor_get(v___x_521_, 6);
v_messages_528_ = lean_ctor_get(v___x_521_, 7);
v_infoState_529_ = lean_ctor_get(v___x_521_, 8);
v_snapshotTasks_530_ = lean_ctor_get(v___x_521_, 9);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_521_, 5);
lean_dec(v_unused_585_);
v___x_532_ = v___x_521_;
v_isShared_533_ = v_isSharedCheck_584_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snapshotTasks_530_);
lean_inc(v_infoState_529_);
lean_inc(v_messages_528_);
lean_inc(v_recordedDeps_527_);
lean_inc(v_traceState_526_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_521_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_584_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_534_ = l_Lean_Environment_setExporting(v_env_522_, v_isExporting_508_);
v___x_535_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 5, v___x_535_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_traceState_526_);
lean_ctor_set(v_reuseFailAlloc_583_, 5, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_583_, 6, v_recordedDeps_527_);
lean_ctor_set(v_reuseFailAlloc_583_, 7, v_messages_528_);
lean_ctor_set(v_reuseFailAlloc_583_, 8, v_infoState_529_);
lean_ctor_set(v_reuseFailAlloc_583_, 9, v_snapshotTasks_530_);
v___x_537_ = v_reuseFailAlloc_583_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_mctx_540_; lean_object* v_zetaDeltaFVarIds_541_; lean_object* v_postponed_542_; lean_object* v_diag_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_581_; 
v___x_538_ = lean_st_ref_put(v___y_512_, v___x_537_);
v___x_539_ = lean_st_ref_take(v___y_510_);
v_mctx_540_ = lean_ctor_get(v___x_539_, 0);
v_zetaDeltaFVarIds_541_ = lean_ctor_get(v___x_539_, 2);
v_postponed_542_ = lean_ctor_get(v___x_539_, 3);
v_diag_543_ = lean_ctor_get(v___x_539_, 4);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_539_, 1);
lean_dec(v_unused_582_);
v___x_545_ = v___x_539_;
v_isShared_546_ = v_isSharedCheck_581_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_diag_543_);
lean_inc(v_postponed_542_);
lean_inc(v_zetaDeltaFVarIds_541_);
lean_inc(v_mctx_540_);
lean_dec(v___x_539_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_581_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_mctx_540_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_zetaDeltaFVarIds_541_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_postponed_542_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_diag_543_);
v___x_549_ = v_reuseFailAlloc_580_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v_r_551_; 
v___x_550_ = lean_st_ref_put(v___y_510_, v___x_549_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
v_r_551_ = lean_apply_5(v_x_507_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, lean_box(0));
if (lean_obj_tag(v_r_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_568_; 
v_a_552_ = lean_ctor_get(v_r_551_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_r_551_);
if (v_isSharedCheck_568_ == 0)
{
v___x_554_ = v_r_551_;
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v_r_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
lean_inc(v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set_tag(v___x_554_, 1);
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_567_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v___x_558_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(v___y_512_, v_isExporting_519_, v___x_535_, v___y_510_, v___x_547_, v___x_557_);
lean_dec_ref(v___x_557_);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_558_, 0);
lean_dec(v_unused_566_);
v___x_560_ = v___x_558_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_dec(v___x_558_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_a_552_);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_552_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_a_569_ = lean_ctor_get(v_r_551_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v_r_551_, 1);
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(v___y_512_, v_isExporting_519_, v___x_535_, v___y_510_, v___x_547_, v___x_570_);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_571_, 0);
lean_dec(v_unused_579_);
v___x_573_ = v___x_571_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_dec(v___x_571_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 1);
lean_ctor_set(v___x_573_, 0, v_a_569_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_569_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___boxed(lean_object* v_x_588_, lean_object* v_isExporting_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v_isExporting_boxed_595_; lean_object* v_res_596_; 
v_isExporting_boxed_595_ = lean_unbox(v_isExporting_589_);
v_res_596_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_588_, v_isExporting_boxed_595_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_x_597_, uint8_t v_when_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
if (v_when_598_ == 0)
{
lean_object* v___x_604_; 
lean_inc(v___y_602_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
v___x_604_ = lean_apply_5(v_x_597_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
return v___x_604_;
}
else
{
uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_605_ = 0;
v___x_606_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_597_, v___x_605_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object* v_x_607_, lean_object* v_when_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v_when_boxed_614_; lean_object* v_res_615_; 
v_when_boxed_614_ = lean_unbox(v_when_608_);
v_res_615_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v_x_607_, v_when_boxed_614_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_ref_616_, lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_toCold_623_; lean_object* v_currRecDepth_624_; lean_object* v_ref_625_; uint16_t v_optionFlags_626_; uint8_t v_suppressElabErrors_627_; uint8_t v_checkDeprecated_628_; uint8_t v_isRecordingDeps_629_; lean_object* v_ref_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_toCold_623_ = lean_ctor_get(v___y_620_, 0);
v_currRecDepth_624_ = lean_ctor_get(v___y_620_, 1);
v_ref_625_ = lean_ctor_get(v___y_620_, 2);
v_optionFlags_626_ = lean_ctor_get_uint16(v___y_620_, sizeof(void*)*3);
v_suppressElabErrors_627_ = lean_ctor_get_uint8(v___y_620_, sizeof(void*)*3 + 2);
v_checkDeprecated_628_ = lean_ctor_get_uint8(v___y_620_, sizeof(void*)*3 + 3);
v_isRecordingDeps_629_ = lean_ctor_get_uint8(v___y_620_, sizeof(void*)*3 + 4);
v_ref_630_ = l_Lean_replaceRef(v_ref_616_, v_ref_625_);
lean_inc(v_currRecDepth_624_);
lean_inc_ref(v_toCold_623_);
v___x_631_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_631_, 0, v_toCold_623_);
lean_ctor_set(v___x_631_, 1, v_currRecDepth_624_);
lean_ctor_set(v___x_631_, 2, v_ref_630_);
lean_ctor_set_uint16(v___x_631_, sizeof(void*)*3, v_optionFlags_626_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 2, v_suppressElabErrors_627_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 3, v_checkDeprecated_628_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 4, v_isRecordingDeps_629_);
v___x_632_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_617_, v___y_618_, v___y_619_, v___x_631_, v___y_621_);
lean_dec_ref_known(v___x_631_, 3);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_ref_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_633_, v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v_ref_633_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(lean_object* v_declName_641_, uint8_t v_s_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_env_647_; lean_object* v_nextMacroScope_648_; lean_object* v_ngen_649_; lean_object* v_auxDeclNGen_650_; lean_object* v_traceState_651_; lean_object* v_recordedDeps_652_; lean_object* v_messages_653_; lean_object* v_infoState_654_; lean_object* v_snapshotTasks_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_684_; 
v___x_646_ = lean_st_ref_take(v___y_644_);
v_env_647_ = lean_ctor_get(v___x_646_, 0);
v_nextMacroScope_648_ = lean_ctor_get(v___x_646_, 1);
v_ngen_649_ = lean_ctor_get(v___x_646_, 2);
v_auxDeclNGen_650_ = lean_ctor_get(v___x_646_, 3);
v_traceState_651_ = lean_ctor_get(v___x_646_, 4);
v_recordedDeps_652_ = lean_ctor_get(v___x_646_, 6);
v_messages_653_ = lean_ctor_get(v___x_646_, 7);
v_infoState_654_ = lean_ctor_get(v___x_646_, 8);
v_snapshotTasks_655_ = lean_ctor_get(v___x_646_, 9);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v___x_646_, 5);
lean_dec(v_unused_685_);
v___x_657_ = v___x_646_;
v_isShared_658_ = v_isSharedCheck_684_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snapshotTasks_655_);
lean_inc(v_infoState_654_);
lean_inc(v_messages_653_);
lean_inc(v_recordedDeps_652_);
lean_inc(v_traceState_651_);
lean_inc(v_auxDeclNGen_650_);
lean_inc(v_ngen_649_);
lean_inc(v_nextMacroScope_648_);
lean_inc(v_env_647_);
lean_dec(v___x_646_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_684_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_659_ = 0;
v___x_660_ = lean_box(0);
v___x_661_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_647_, v_declName_641_, v_s_642_, v___x_659_, v___x_660_);
v___x_662_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 5, v___x_662_);
lean_ctor_set(v___x_657_, 0, v___x_661_);
v___x_664_ = v___x_657_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_nextMacroScope_648_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_ngen_649_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_auxDeclNGen_650_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_traceState_651_);
lean_ctor_set(v_reuseFailAlloc_683_, 5, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_683_, 6, v_recordedDeps_652_);
lean_ctor_set(v_reuseFailAlloc_683_, 7, v_messages_653_);
lean_ctor_set(v_reuseFailAlloc_683_, 8, v_infoState_654_);
lean_ctor_set(v_reuseFailAlloc_683_, 9, v_snapshotTasks_655_);
v___x_664_ = v_reuseFailAlloc_683_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_mctx_667_; lean_object* v_zetaDeltaFVarIds_668_; lean_object* v_postponed_669_; lean_object* v_diag_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_681_; 
v___x_665_ = lean_st_ref_put(v___y_644_, v___x_664_);
v___x_666_ = lean_st_ref_take(v___y_643_);
v_mctx_667_ = lean_ctor_get(v___x_666_, 0);
v_zetaDeltaFVarIds_668_ = lean_ctor_get(v___x_666_, 2);
v_postponed_669_ = lean_ctor_get(v___x_666_, 3);
v_diag_670_ = lean_ctor_get(v___x_666_, 4);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_666_, 1);
lean_dec(v_unused_682_);
v___x_672_ = v___x_666_;
v_isShared_673_ = v_isSharedCheck_681_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_diag_670_);
lean_inc(v_postponed_669_);
lean_inc(v_zetaDeltaFVarIds_668_);
lean_inc(v_mctx_667_);
lean_dec(v___x_666_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_681_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_box(0);
v___x_675_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_mctx_667_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_zetaDeltaFVarIds_668_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_postponed_669_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_diag_670_);
v___x_677_ = v_reuseFailAlloc_680_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_st_ref_put(v___y_643_, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_674_);
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg___boxed(lean_object* v_declName_686_, lean_object* v_s_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_s_boxed_691_; lean_object* v_res_692_; 
v_s_boxed_691_ = lean_unbox(v_s_687_);
v_res_692_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_686_, v_s_boxed_691_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_declName_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_699_; lean_object* v___x_700_; 
v___x_699_ = 0;
v___x_700_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_693_, v___x_699_, v___y_695_, v___y_697_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_declName_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(v_declName_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__0));
v___x_710_ = l_Lean_stringToMessageData(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__2));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__4));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__6));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__8));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v___x_723_, lean_object* v_projName_724_, lean_object* v___x_725_, lean_object* v_a_726_, uint8_t v_instImplicit_727_, lean_object* v___x_728_, lean_object* v_params_729_, lean_object* v_self_730_, lean_object* v_b_731_, uint8_t v___x_732_, lean_object* v_a_733_, lean_object* v___x_734_, lean_object* v_paramInfoOverrides_735_, lean_object* v_n_736_, lean_object* v_ref_737_, lean_object* v___x_738_, uint8_t v_a_739_, lean_object* v_____r_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_805_; lean_object* v___y_806_; uint8_t v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_817_; uint8_t v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = l_List_lengthTR___redArg(v_paramInfoOverrides_735_);
v___x_910_ = lean_array_get_size(v_params_729_);
v___x_911_ = lean_nat_dec_le(v___x_909_, v___x_910_);
lean_dec(v___x_909_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_912_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
lean_inc(v_projName_724_);
v___x_913_ = l_Lean_MessageData_ofName(v_projName_724_);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
lean_inc(v_n_736_);
v___x_917_ = l_Lean_MessageData_ofConstName(v_n_736_, v___x_911_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_737_, v___x_920_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref_known(v___x_921_, 1);
goto v___jp_870_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v___x_738_);
lean_dec(v_n_736_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
goto v___jp_870_;
}
v___jp_746_:
{
lean_object* v___x_749_; lean_object* v_env_750_; lean_object* v_nextMacroScope_751_; lean_object* v_ngen_752_; lean_object* v_auxDeclNGen_753_; lean_object* v_traceState_754_; lean_object* v_recordedDeps_755_; lean_object* v_messages_756_; lean_object* v_infoState_757_; lean_object* v_snapshotTasks_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_790_; 
v___x_749_ = lean_st_ref_take(v___y_748_);
v_env_750_ = lean_ctor_get(v___x_749_, 0);
v_nextMacroScope_751_ = lean_ctor_get(v___x_749_, 1);
v_ngen_752_ = lean_ctor_get(v___x_749_, 2);
v_auxDeclNGen_753_ = lean_ctor_get(v___x_749_, 3);
v_traceState_754_ = lean_ctor_get(v___x_749_, 4);
v_recordedDeps_755_ = lean_ctor_get(v___x_749_, 6);
v_messages_756_ = lean_ctor_get(v___x_749_, 7);
v_infoState_757_ = lean_ctor_get(v___x_749_, 8);
v_snapshotTasks_758_ = lean_ctor_get(v___x_749_, 9);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_749_, 5);
lean_dec(v_unused_791_);
v___x_760_ = v___x_749_;
v_isShared_761_ = v_isSharedCheck_790_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snapshotTasks_758_);
lean_inc(v_infoState_757_);
lean_inc(v_messages_756_);
lean_inc(v_recordedDeps_755_);
lean_inc(v_traceState_754_);
lean_inc(v_auxDeclNGen_753_);
lean_inc(v_ngen_752_);
lean_inc(v_nextMacroScope_751_);
lean_inc(v_env_750_);
lean_dec(v___x_749_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_790_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_name_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v_name_762_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_name_762_);
lean_dec_ref(v___x_723_);
lean_inc(v_projName_724_);
v___x_763_ = l_Lean_addProjectionFnInfo(v_env_750_, v_projName_724_, v_name_762_, v___x_725_, v_a_726_, v_instImplicit_727_);
v___x_764_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 5, v___x_764_);
lean_ctor_set(v___x_760_, 0, v___x_763_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_nextMacroScope_751_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_ngen_752_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_auxDeclNGen_753_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_traceState_754_);
lean_ctor_set(v_reuseFailAlloc_789_, 5, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_789_, 6, v_recordedDeps_755_);
lean_ctor_set(v_reuseFailAlloc_789_, 7, v_messages_756_);
lean_ctor_set(v_reuseFailAlloc_789_, 8, v_infoState_757_);
lean_ctor_set(v_reuseFailAlloc_789_, 9, v_snapshotTasks_758_);
v___x_766_ = v_reuseFailAlloc_789_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_mctx_769_; lean_object* v_zetaDeltaFVarIds_770_; lean_object* v_postponed_771_; lean_object* v_diag_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_787_; 
v___x_767_ = lean_st_ref_put(v___y_748_, v___x_766_);
v___x_768_ = lean_st_ref_take(v___y_747_);
v_mctx_769_ = lean_ctor_get(v___x_768_, 0);
v_zetaDeltaFVarIds_770_ = lean_ctor_get(v___x_768_, 2);
v_postponed_771_ = lean_ctor_get(v___x_768_, 3);
v_diag_772_ = lean_ctor_get(v___x_768_, 4);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v___x_768_, 1);
lean_dec(v_unused_788_);
v___x_774_ = v___x_768_;
v_isShared_775_ = v_isSharedCheck_787_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_diag_772_);
lean_inc(v_postponed_771_);
lean_inc(v_zetaDeltaFVarIds_770_);
lean_inc(v_mctx_769_);
lean_dec(v___x_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_787_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__5);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_mctx_769_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_zetaDeltaFVarIds_770_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_postponed_771_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_diag_772_);
v___x_778_ = v_reuseFailAlloc_786_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_779_ = lean_st_ref_put(v___y_747_, v___x_778_);
v___x_780_ = l_Lean_Expr_const___override(v_projName_724_, v___x_728_);
v___x_781_ = l_Lean_mkAppN(v___x_780_, v_params_729_);
v___x_782_ = l_Lean_Expr_app___override(v___x_781_, v_self_730_);
v___x_783_ = l_Lean_Expr_bindingBody_x21(v_b_731_);
v___x_784_ = lean_expr_instantiate1(v___x_783_, v___x_782_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
}
}
}
v___jp_792_:
{
if (lean_obj_tag(v___y_795_) == 0)
{
lean_dec_ref_known(v___y_795_, 1);
v___y_747_ = v___y_793_;
v___y_748_ = v___y_794_;
goto v___jp_746_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_796_ = lean_ctor_get(v___y_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___y_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___y_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___y_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
v___jp_804_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = lean_box(0);
lean_inc(v_projName_724_);
v___x_812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_812_, 0, v_projName_724_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_813_, 0, v___y_809_);
lean_ctor_set(v___x_813_, 1, v___y_806_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*3, v___x_732_);
v___x_814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = l_Lean_addDecl(v___x_814_, v___y_807_, v___y_810_, v___y_808_);
lean_dec_ref(v___y_810_);
v___y_793_ = v___y_805_;
v___y_794_ = v___y_808_;
v___y_795_ = v___x_815_;
goto v___jp_792_;
}
v___jp_816_:
{
uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v_toCold_825_; lean_object* v_currRecDepth_826_; lean_object* v_ref_827_; uint16_t v_optionFlags_828_; uint8_t v_suppressElabErrors_829_; uint8_t v_checkDeprecated_830_; uint8_t v_isRecordingDeps_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_ref_836_; lean_object* v___x_837_; 
v___x_823_ = 0;
lean_inc_ref(v_a_733_);
v___x_824_ = l_Lean_LocalContext_mkForall(v_a_733_, v___x_734_, v___y_817_, v___x_732_, v___x_823_);
lean_dec_ref(v___y_817_);
v_toCold_825_ = lean_ctor_get(v___y_821_, 0);
v_currRecDepth_826_ = lean_ctor_get(v___y_821_, 1);
v_ref_827_ = lean_ctor_get(v___y_821_, 2);
v_optionFlags_828_ = lean_ctor_get_uint16(v___y_821_, sizeof(void*)*3);
v_suppressElabErrors_829_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*3 + 2);
v_checkDeprecated_830_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*3 + 3);
v_isRecordingDeps_831_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*3 + 4);
v___x_832_ = l_Lean_Expr_inferImplicit(v___x_824_, v___x_725_, v___x_732_);
v___x_833_ = l_Lean_Expr_updateForallBinderInfos(v___x_832_, v_paramInfoOverrides_735_);
lean_inc_ref(v_self_730_);
lean_inc(v_a_726_);
v___x_834_ = l_Lean_Expr_proj___override(v_n_736_, v_a_726_, v_self_730_);
v___x_835_ = l_Lean_LocalContext_mkLambda(v_a_733_, v___x_734_, v___x_834_, v___x_732_, v___x_823_);
lean_dec_ref(v___x_834_);
v_ref_836_ = l_Lean_replaceRef(v_ref_737_, v_ref_827_);
lean_inc(v_currRecDepth_826_);
lean_inc_ref(v_toCold_825_);
v___x_837_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_837_, 0, v_toCold_825_);
lean_ctor_set(v___x_837_, 1, v_currRecDepth_826_);
lean_ctor_set(v___x_837_, 2, v_ref_836_);
lean_ctor_set_uint16(v___x_837_, sizeof(void*)*3, v_optionFlags_828_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*3 + 2, v_suppressElabErrors_829_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*3 + 3, v_checkDeprecated_830_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*3 + 4, v_isRecordingDeps_831_);
if (v___y_818_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(1);
lean_inc(v_projName_724_);
v___x_839_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(v_projName_724_, v___x_738_, v___x_833_, v___x_835_, v___x_838_, v___y_822_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_a_840_);
v___x_842_ = l_Lean_addDecl(v___x_841_, v___x_823_, v___x_837_, v___y_822_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_dec_ref_known(v___x_842_, 1);
if (v_instImplicit_727_ == 0)
{
lean_object* v___x_843_; 
lean_inc(v_projName_724_);
v___x_843_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(v_projName_724_, v___y_819_, v___y_820_, v___x_837_, v___y_822_);
lean_dec_ref_known(v___x_837_, 3);
v___y_793_ = v___y_820_;
v___y_794_ = v___y_822_;
v___y_795_ = v___x_843_;
goto v___jp_792_;
}
else
{
lean_dec_ref_known(v___x_837_, 3);
v___y_747_ = v___y_820_;
v___y_748_ = v___y_822_;
goto v___jp_746_;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref_known(v___x_837_, 3);
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_844_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref_known(v___x_837_, 3);
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_852_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_839_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_839_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_env_862_; uint8_t v___x_863_; 
lean_inc_ref(v___x_833_);
lean_inc(v_projName_724_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_projName_724_);
lean_ctor_set(v___x_860_, 1, v___x_738_);
lean_ctor_set(v___x_860_, 2, v___x_833_);
v___x_861_ = lean_st_ref_get(v___y_822_);
v_env_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref_n(v_env_862_, 2);
lean_dec(v___x_861_);
v___x_863_ = l_Lean_Environment_hasUnsafe(v_env_862_, v___x_833_);
lean_dec_ref(v___x_833_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_Environment_hasUnsafe(v_env_862_, v___x_835_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_865_ = lean_box(0);
lean_inc(v_projName_724_);
v___x_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_866_, 0, v_projName_724_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_860_);
lean_ctor_set(v___x_867_, 1, v___x_835_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
v___x_868_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = l_Lean_addDecl(v___x_868_, v___x_823_, v___x_837_, v___y_822_);
lean_dec_ref_known(v___x_837_, 3);
v___y_793_ = v___y_820_;
v___y_794_ = v___y_822_;
v___y_795_ = v___x_869_;
goto v___jp_792_;
}
else
{
v___y_805_ = v___y_820_;
v___y_806_ = v___x_835_;
v___y_807_ = v___x_823_;
v___y_808_ = v___y_822_;
v___y_809_ = v___x_860_;
v___y_810_ = v___x_837_;
goto v___jp_804_;
}
}
else
{
lean_dec_ref(v_env_862_);
v___y_805_ = v___y_820_;
v___y_806_ = v___x_835_;
v___y_807_ = v___x_823_;
v___y_808_ = v___y_822_;
v___y_809_ = v___x_860_;
v___y_810_ = v___x_837_;
goto v___jp_804_;
}
}
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_Expr_bindingDomain_x21(v_b_731_);
v___x_872_ = lean_expr_consume_type_annotations(v___x_871_);
lean_inc_ref(v___x_872_);
v___x_873_ = l_Lean_Meta_isProp(v___x_872_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_873_) == 0)
{
if (v_a_739_ == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = lean_unbox(v_a_874_);
lean_dec(v_a_874_);
v___y_817_ = v___x_872_;
v___y_818_ = v___x_875_;
v___y_819_ = v___y_741_;
v___y_820_ = v___y_742_;
v___y_821_ = v___y_743_;
v___y_822_ = v___y_744_;
goto v___jp_816_;
}
else
{
lean_object* v_a_876_; uint8_t v___x_877_; 
v_a_876_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v___x_873_, 1);
v___x_877_ = lean_unbox(v_a_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_878_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
lean_inc(v_projName_724_);
v___x_879_ = l_Lean_MessageData_ofName(v_projName_724_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_unbox(v_a_876_);
lean_inc(v_n_736_);
v___x_884_ = l_Lean_MessageData_ofConstName(v_n_736_, v___x_883_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
lean_inc_ref(v___x_872_);
v___x_888_ = l_Lean_indentExpr(v___x_872_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_737_, v___x_889_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_890_) == 0)
{
uint8_t v___x_891_; 
lean_dec_ref_known(v___x_890_, 1);
v___x_891_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___y_817_ = v___x_872_;
v___y_818_ = v___x_891_;
v___y_819_ = v___y_741_;
v___y_820_ = v___y_742_;
v___y_821_ = v___y_743_;
v___y_822_ = v___y_744_;
goto v___jp_816_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_876_);
lean_dec_ref(v___x_872_);
lean_dec(v___x_738_);
lean_dec(v_n_736_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_892_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_890_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_890_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
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
else
{
uint8_t v___x_900_; 
v___x_900_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___y_817_ = v___x_872_;
v___y_818_ = v___x_900_;
v___y_819_ = v___y_741_;
v___y_820_ = v___y_742_;
v___y_821_ = v___y_743_;
v___y_822_ = v___y_744_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___x_872_);
lean_dec(v___x_738_);
lean_dec(v_n_736_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_self_730_);
lean_dec(v___x_728_);
lean_dec(v_a_726_);
lean_dec(v___x_725_);
lean_dec(v_projName_724_);
lean_dec_ref(v___x_723_);
v_a_901_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_873_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_873_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_930_ = _args[0];
lean_object* v_projName_931_ = _args[1];
lean_object* v___x_932_ = _args[2];
lean_object* v_a_933_ = _args[3];
lean_object* v_instImplicit_934_ = _args[4];
lean_object* v___x_935_ = _args[5];
lean_object* v_params_936_ = _args[6];
lean_object* v_self_937_ = _args[7];
lean_object* v_b_938_ = _args[8];
lean_object* v___x_939_ = _args[9];
lean_object* v_a_940_ = _args[10];
lean_object* v___x_941_ = _args[11];
lean_object* v_paramInfoOverrides_942_ = _args[12];
lean_object* v_n_943_ = _args[13];
lean_object* v_ref_944_ = _args[14];
lean_object* v___x_945_ = _args[15];
lean_object* v_a_946_ = _args[16];
lean_object* v_____r_947_ = _args[17];
lean_object* v___y_948_ = _args[18];
lean_object* v___y_949_ = _args[19];
lean_object* v___y_950_ = _args[20];
lean_object* v___y_951_ = _args[21];
lean_object* v___y_952_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_953_; uint8_t v___x_18644__boxed_954_; uint8_t v_a_18650__boxed_955_; lean_object* v_res_956_; 
v_instImplicit_boxed_953_ = lean_unbox(v_instImplicit_934_);
v___x_18644__boxed_954_ = lean_unbox(v___x_939_);
v_a_18650__boxed_955_ = lean_unbox(v_a_946_);
v_res_956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v___x_930_, v_projName_931_, v___x_932_, v_a_933_, v_instImplicit_boxed_953_, v___x_935_, v_params_936_, v_self_937_, v_b_938_, v___x_18644__boxed_954_, v_a_940_, v___x_941_, v_paramInfoOverrides_942_, v_n_943_, v_ref_944_, v___x_945_, v_a_18650__boxed_955_, v_____r_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v_ref_944_);
lean_dec(v_paramInfoOverrides_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v_b_938_);
lean_dec_ref(v_params_936_);
return v_res_956_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(uint8_t v___x_960_, lean_object* v_projName_961_, lean_object* v_n_962_, lean_object* v_ref_963_, lean_object* v___f_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
if (v___x_960_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_970_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
v___x_971_ = l_Lean_MessageData_ofName(v_projName_961_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = l_Lean_MessageData_ofConstName(v_n_962_, v___x_960_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_963_, v___x_978_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
v___x_981_ = lean_apply_6(v___f_964_, v_a_980_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, lean_box(0));
return v___x_981_;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v___f_964_);
v_a_982_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_979_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_979_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_n_962_);
lean_dec(v_projName_961_);
v___x_990_ = lean_box(0);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc_ref(v___y_965_);
v___x_991_ = lean_apply_6(v___f_964_, v___x_990_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, lean_box(0));
return v___x_991_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___boxed(lean_object* v___x_992_, lean_object* v_projName_993_, lean_object* v_n_994_, lean_object* v_ref_995_, lean_object* v___f_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___x_19043__boxed_1002_; lean_object* v_res_1003_; 
v___x_19043__boxed_1002_ = lean_unbox(v___x_992_);
v_res_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(v___x_19043__boxed_1002_, v_projName_993_, v_n_994_, v_ref_995_, v___f_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v_ref_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_upperBound_1004_, lean_object* v_projDecls_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, uint8_t v_instImplicit_1008_, lean_object* v___x_1009_, lean_object* v_params_1010_, lean_object* v_self_1011_, lean_object* v_a_1012_, lean_object* v___x_1013_, lean_object* v_n_1014_, lean_object* v___x_1015_, uint8_t v_a_1016_, lean_object* v_a_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_nat_dec_lt(v_a_1017_, v_upperBound_1004_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v_a_1017_);
lean_dec(v___x_1015_);
lean_dec(v_n_1014_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_a_1012_);
lean_dec_ref(v_self_1011_);
lean_dec_ref(v_params_1010_);
lean_dec(v___x_1009_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1006_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_b_1018_);
return v___x_1025_;
}
else
{
lean_object* v___x_1026_; lean_object* v_ref_1027_; lean_object* v_projName_1028_; lean_object* v_paramInfoOverrides_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___y_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1026_ = lean_array_fget_borrowed(v_projDecls_1005_, v_a_1017_);
v_ref_1027_ = lean_ctor_get(v___x_1026_, 0);
v_projName_1028_ = lean_ctor_get(v___x_1026_, 1);
v_paramInfoOverrides_1029_ = lean_ctor_get(v___x_1026_, 2);
v___x_1030_ = lean_box(v_instImplicit_1008_);
v___x_1031_ = lean_box(v___x_1024_);
v___x_1032_ = lean_box(v_a_1016_);
lean_inc(v___x_1015_);
lean_inc_n(v_ref_1027_, 2);
lean_inc_n(v_n_1014_, 2);
lean_inc(v_paramInfoOverrides_1029_);
lean_inc_ref(v___x_1013_);
lean_inc_ref(v_a_1012_);
lean_inc_ref(v_b_1018_);
lean_inc_ref(v_self_1011_);
lean_inc_ref(v_params_1010_);
lean_inc(v___x_1009_);
lean_inc(v_a_1017_);
lean_inc(v___x_1007_);
lean_inc_n(v_projName_1028_, 2);
lean_inc_ref(v___x_1006_);
v___f_1033_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_1033_, 0, v___x_1006_);
lean_closure_set(v___f_1033_, 1, v_projName_1028_);
lean_closure_set(v___f_1033_, 2, v___x_1007_);
lean_closure_set(v___f_1033_, 3, v_a_1017_);
lean_closure_set(v___f_1033_, 4, v___x_1030_);
lean_closure_set(v___f_1033_, 5, v___x_1009_);
lean_closure_set(v___f_1033_, 6, v_params_1010_);
lean_closure_set(v___f_1033_, 7, v_self_1011_);
lean_closure_set(v___f_1033_, 8, v_b_1018_);
lean_closure_set(v___f_1033_, 9, v___x_1031_);
lean_closure_set(v___f_1033_, 10, v_a_1012_);
lean_closure_set(v___f_1033_, 11, v___x_1013_);
lean_closure_set(v___f_1033_, 12, v_paramInfoOverrides_1029_);
lean_closure_set(v___f_1033_, 13, v_n_1014_);
lean_closure_set(v___f_1033_, 14, v_ref_1027_);
lean_closure_set(v___f_1033_, 15, v___x_1015_);
lean_closure_set(v___f_1033_, 16, v___x_1032_);
v___x_1034_ = l_Lean_Expr_isForall(v_b_1018_);
lean_dec_ref(v_b_1018_);
v___x_1035_ = lean_box(v___x_1034_);
v___y_1036_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_1036_, 0, v___x_1035_);
lean_closure_set(v___y_1036_, 1, v_projName_1028_);
lean_closure_set(v___y_1036_, 2, v_n_1014_);
lean_closure_set(v___y_1036_, 3, v_ref_1027_);
lean_closure_set(v___y_1036_, 4, v___f_1033_);
v___x_1037_ = l_Lean_isPrivateName(v_projName_1028_);
v___x_1038_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v___y_1036_, v___x_1037_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_add(v_a_1017_, v___x_1040_);
lean_dec(v_a_1017_);
v_a_1017_ = v___x_1041_;
v_b_1018_ = v_a_1039_;
goto _start;
}
else
{
lean_dec(v_a_1017_);
lean_dec(v___x_1015_);
lean_dec(v_n_1014_);
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_a_1012_);
lean_dec_ref(v_self_1011_);
lean_dec_ref(v_params_1010_);
lean_dec(v___x_1009_);
lean_dec(v___x_1007_);
lean_dec_ref(v___x_1006_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1043_ = _args[0];
lean_object* v_projDecls_1044_ = _args[1];
lean_object* v___x_1045_ = _args[2];
lean_object* v___x_1046_ = _args[3];
lean_object* v_instImplicit_1047_ = _args[4];
lean_object* v___x_1048_ = _args[5];
lean_object* v_params_1049_ = _args[6];
lean_object* v_self_1050_ = _args[7];
lean_object* v_a_1051_ = _args[8];
lean_object* v___x_1052_ = _args[9];
lean_object* v_n_1053_ = _args[10];
lean_object* v___x_1054_ = _args[11];
lean_object* v_a_1055_ = _args[12];
lean_object* v_a_1056_ = _args[13];
lean_object* v_b_1057_ = _args[14];
lean_object* v___y_1058_ = _args[15];
lean_object* v___y_1059_ = _args[16];
lean_object* v___y_1060_ = _args[17];
lean_object* v___y_1061_ = _args[18];
lean_object* v___y_1062_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1063_; uint8_t v_a_19124__boxed_1064_; lean_object* v_res_1065_; 
v_instImplicit_boxed_1063_ = lean_unbox(v_instImplicit_1047_);
v_a_19124__boxed_1064_ = lean_unbox(v_a_1055_);
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v_upperBound_1043_, v_projDecls_1044_, v___x_1045_, v___x_1046_, v_instImplicit_boxed_1063_, v___x_1048_, v_params_1049_, v_self_1050_, v_a_1051_, v___x_1052_, v_n_1053_, v___x_1054_, v_a_19124__boxed_1064_, v_a_1056_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_projDecls_1044_);
lean_dec(v_upperBound_1043_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1066_, uint8_t v_instImplicit_1067_, lean_object* v_projDecls_1068_, lean_object* v_toConstantVal_1069_, lean_object* v_numParams_1070_, lean_object* v___x_1071_, lean_object* v_n_1072_, lean_object* v_levelParams_1073_, uint8_t v_a_1074_, lean_object* v_ctorType_1075_, lean_object* v_self_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_lctx_1082_; lean_object* v___x_1083_; size_t v_sz_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v_lctx_1082_ = lean_ctor_get(v___y_1077_, 2);
lean_inc_ref(v_self_1076_);
lean_inc_ref(v_params_1066_);
v___x_1083_ = lean_array_push(v_params_1066_, v_self_1076_);
v_sz_1084_ = lean_array_size(v_params_1066_);
v___x_1085_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1082_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1067_, v_params_1066_, v_sz_1084_, v___x_1085_, v_lctx_1082_, v___y_1077_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = lean_array_get_size(v_projDecls_1068_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1088_, v_projDecls_1068_, v_toConstantVal_1069_, v_numParams_1070_, v_instImplicit_1067_, v___x_1071_, v_params_1066_, v_self_1076_, v_a_1087_, v___x_1083_, v_n_1072_, v_levelParams_1073_, v_a_1074_, v___x_1089_, v_ctorType_1075_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v___x_1090_, 0);
lean_dec(v_unused_1099_);
v___x_1092_ = v___x_1090_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v___x_1090_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_box(0);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1090_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1090_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v___x_1083_);
lean_dec_ref(v_self_1076_);
lean_dec_ref(v_ctorType_1075_);
lean_dec(v_levelParams_1073_);
lean_dec(v_n_1072_);
lean_dec(v___x_1071_);
lean_dec(v_numParams_1070_);
lean_dec_ref(v_toConstantVal_1069_);
lean_dec_ref(v_params_1066_);
v_a_1108_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1086_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1086_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1116_, lean_object* v_instImplicit_1117_, lean_object* v_projDecls_1118_, lean_object* v_toConstantVal_1119_, lean_object* v_numParams_1120_, lean_object* v___x_1121_, lean_object* v_n_1122_, lean_object* v_levelParams_1123_, lean_object* v_a_1124_, lean_object* v_ctorType_1125_, lean_object* v_self_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_instImplicit_boxed_1132_; uint8_t v_a_19196__boxed_1133_; lean_object* v_res_1134_; 
v_instImplicit_boxed_1132_ = lean_unbox(v_instImplicit_1117_);
v_a_19196__boxed_1133_ = lean_unbox(v_a_1124_);
v_res_1134_ = l_Lean_Meta_mkProjections___lam__0(v_params_1116_, v_instImplicit_boxed_1132_, v_projDecls_1118_, v_toConstantVal_1119_, v_numParams_1120_, v___x_1121_, v_n_1122_, v_levelParams_1123_, v_a_19196__boxed_1133_, v_ctorType_1125_, v_self_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v_projDecls_1118_);
return v_res_1134_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1144_, lean_object* v_projDecls_1145_, lean_object* v_toConstantVal_1146_, lean_object* v_numParams_1147_, lean_object* v___x_1148_, lean_object* v_n_1149_, lean_object* v_levelParams_1150_, uint8_t v_a_1151_, lean_object* v_params_1152_, lean_object* v_ctorType_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1170_ = lean_box(v_instImplicit_1144_);
v___x_1171_ = lean_box(v_a_1151_);
lean_inc(v_n_1149_);
lean_inc(v___x_1148_);
lean_inc(v_numParams_1147_);
lean_inc_ref(v_params_1152_);
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1172_, 0, v_params_1152_);
lean_closure_set(v___f_1172_, 1, v___x_1170_);
lean_closure_set(v___f_1172_, 2, v_projDecls_1145_);
lean_closure_set(v___f_1172_, 3, v_toConstantVal_1146_);
lean_closure_set(v___f_1172_, 4, v_numParams_1147_);
lean_closure_set(v___f_1172_, 5, v___x_1148_);
lean_closure_set(v___f_1172_, 6, v_n_1149_);
lean_closure_set(v___f_1172_, 7, v_levelParams_1150_);
lean_closure_set(v___f_1172_, 8, v___x_1171_);
lean_closure_set(v___f_1172_, 9, v_ctorType_1153_);
v___x_1178_ = lean_array_get_size(v_params_1152_);
v___x_1179_ = lean_nat_dec_eq(v___x_1178_, v_numParams_1147_);
lean_dec(v_numParams_1147_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref(v___f_1172_);
lean_dec_ref(v_params_1152_);
lean_dec(v___x_1148_);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1181_ = l_Lean_MessageData_ofConstName(v_n_1149_, v___x_1179_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1184_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1185_;
}
else
{
goto v___jp_1173_;
}
v___jp_1159_:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1168_ = 0;
v___x_1169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(v___x_1167_, v___y_1166_, v___y_1165_, v___y_1164_, v___x_1168_, v___y_1163_, v___y_1162_, v___y_1161_, v___y_1160_);
return v___x_1169_;
}
v___jp_1173_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = l_Lean_Expr_const___override(v_n_1149_, v___x_1148_);
v___x_1175_ = l_Lean_mkAppN(v___x_1174_, v_params_1152_);
lean_dec_ref(v_params_1152_);
if (v_instImplicit_1144_ == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = 0;
v___y_1160_ = v___y_1157_;
v___y_1161_ = v___y_1156_;
v___y_1162_ = v___y_1155_;
v___y_1163_ = v___y_1154_;
v___y_1164_ = v___f_1172_;
v___y_1165_ = v___x_1175_;
v___y_1166_ = v___x_1176_;
goto v___jp_1159_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = 3;
v___y_1160_ = v___y_1157_;
v___y_1161_ = v___y_1156_;
v___y_1162_ = v___y_1155_;
v___y_1163_ = v___y_1154_;
v___y_1164_ = v___f_1172_;
v___y_1165_ = v___x_1175_;
v___y_1166_ = v___x_1177_;
goto v___jp_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1186_, lean_object* v_projDecls_1187_, lean_object* v_toConstantVal_1188_, lean_object* v_numParams_1189_, lean_object* v___x_1190_, lean_object* v_n_1191_, lean_object* v_levelParams_1192_, lean_object* v_a_1193_, lean_object* v_params_1194_, lean_object* v_ctorType_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
uint8_t v_instImplicit_boxed_1201_; uint8_t v_a_19300__boxed_1202_; lean_object* v_res_1203_; 
v_instImplicit_boxed_1201_ = lean_unbox(v_instImplicit_1186_);
v_a_19300__boxed_1202_ = lean_unbox(v_a_1193_);
v_res_1203_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1201_, v_projDecls_1187_, v_toConstantVal_1188_, v_numParams_1189_, v___x_1190_, v_n_1191_, v_levelParams_1192_, v_a_19300__boxed_1202_, v_params_1194_, v_ctorType_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
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
v___x_1218_ = l_instMonadEIO___redArg();
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
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_13659__overap_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_box(0);
v___x_1279_ = l_instInhabitedOfMonad___redArg(v___x_1277_, v___x_1278_);
v___x_13659__overap_1280_ = lean_panic_fn_borrowed(v___x_1279_, v_msg_1223_);
lean_dec(v___x_1279_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1281_ = lean_apply_5(v___x_13659__overap_1280_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
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
lean_object* v_a_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1459_ = l_Lean_InductiveVal_numCtors(v_a_1418_);
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_dec_eq(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec(v_a_1418_);
lean_dec_ref(v_projDecls_1411_);
v___x_1462_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1463_ = l_Lean_MessageData_ofConstName(v_n_1408_, v___x_1461_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1466_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1467_;
}
else
{
v___y_1420_ = v___y_1412_;
v___y_1421_ = v___y_1413_;
v___y_1422_ = v___y_1414_;
v___y_1423_ = v___y_1415_;
goto v___jp_1419_;
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
v___x_1442_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(v_type_1435_, v___x_1440_, v___f_1439_, v___x_1441_, v___x_1441_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
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
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_projDecls_1411_);
lean_dec(v_n_1408_);
v_a_1468_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1417_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1417_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1476_, lean_object* v___x_1477_, lean_object* v_instImplicit_1478_, lean_object* v_projDecls_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
uint8_t v_instImplicit_boxed_1485_; lean_object* v_res_1486_; 
v_instImplicit_boxed_1485_ = lean_unbox(v_instImplicit_1478_);
v_res_1486_ = l_Lean_Meta_mkProjections___lam__2(v_n_1476_, v___x_1477_, v_instImplicit_boxed_1485_, v_projDecls_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___x_1477_);
return v_res_1486_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(32u);
v___x_1490_ = lean_mk_empty_array_with_capacity(v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1492_ = ((size_t)5ULL);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_unsigned_to_nat(32u);
v___x_1495_ = lean_mk_empty_array_with_capacity(v___x_1494_);
v___x_1496_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1497_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___x_1495_);
lean_ctor_set(v___x_1497_, 2, v___x_1493_);
lean_ctor_set(v___x_1497_, 3, v___x_1493_);
lean_ctor_set_usize(v___x_1497_, 4, v___x_1492_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = lean_box(1);
v___x_1499_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1500_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___x_1499_);
lean_ctor_set(v___x_1501_, 2, v___x_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1504_, lean_object* v_projDecls_1505_, uint8_t v_instImplicit_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_box(v_instImplicit_1506_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1514_, 0, v_n_1504_);
lean_closure_set(v___f_1514_, 1, v___x_1512_);
lean_closure_set(v___f_1514_, 2, v___x_1513_);
lean_closure_set(v___f_1514_, 3, v_projDecls_1505_);
v___x_1515_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1516_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1517_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(v___x_1515_, v___x_1516_, v___f_1514_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1518_, lean_object* v_projDecls_1519_, lean_object* v_instImplicit_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
uint8_t v_instImplicit_boxed_1526_; lean_object* v_res_1527_; 
v_instImplicit_boxed_1526_ = lean_unbox(v_instImplicit_1520_);
v_res_1527_ = l_Lean_Meta_mkProjections(v_n_1518_, v_projDecls_1519_, v_instImplicit_boxed_1526_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1528_, lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1528_, v_as_1529_, v_sz_1530_, v_i_1531_, v_b_1532_, v___y_1533_, v___y_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v_instImplicit_boxed_1549_; size_t v_sz_boxed_1550_; size_t v_i_boxed_1551_; lean_object* v_res_1552_; 
v_instImplicit_boxed_1549_ = lean_unbox(v_instImplicit_1539_);
v_sz_boxed_1550_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1551_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1549_, v_as_1540_, v_sz_boxed_1550_, v_i_boxed_1551_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_as_1540_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5(lean_object* v_00_u03b2_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg(){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v___dummy_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg();
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_00_u03b2_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1561_, lean_object* v_ref_1562_, lean_object* v_msg_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_1562_, v_msg_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_ref_1571_, lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1570_, v_ref_1571_, v_msg_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v_ref_1571_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_00_u03b1_1579_, lean_object* v_x_1580_, uint8_t v_when_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v_x_1580_, v_when_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_x_1589_, lean_object* v_when_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
uint8_t v_when_boxed_1596_; lean_object* v_res_1597_; 
v_when_boxed_1596_ = lean_unbox(v_when_1590_);
v_res_1597_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8(v_00_u03b1_1588_, v_x_1589_, v_when_boxed_1596_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_upperBound_1598_, lean_object* v_projDecls_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, uint8_t v_instImplicit_1602_, lean_object* v___x_1603_, lean_object* v_params_1604_, lean_object* v_self_1605_, lean_object* v_a_1606_, lean_object* v___x_1607_, lean_object* v_n_1608_, lean_object* v___x_1609_, uint8_t v_a_1610_, lean_object* v_inst_1611_, lean_object* v_R_1612_, lean_object* v_a_1613_, lean_object* v_b_1614_, lean_object* v_c_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v_upperBound_1598_, v_projDecls_1599_, v___x_1600_, v___x_1601_, v_instImplicit_1602_, v___x_1603_, v_params_1604_, v_self_1605_, v_a_1606_, v___x_1607_, v_n_1608_, v___x_1609_, v_a_1610_, v_a_1613_, v_b_1614_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1622_ = _args[0];
lean_object* v_projDecls_1623_ = _args[1];
lean_object* v___x_1624_ = _args[2];
lean_object* v___x_1625_ = _args[3];
lean_object* v_instImplicit_1626_ = _args[4];
lean_object* v___x_1627_ = _args[5];
lean_object* v_params_1628_ = _args[6];
lean_object* v_self_1629_ = _args[7];
lean_object* v_a_1630_ = _args[8];
lean_object* v___x_1631_ = _args[9];
lean_object* v_n_1632_ = _args[10];
lean_object* v___x_1633_ = _args[11];
lean_object* v_a_1634_ = _args[12];
lean_object* v_inst_1635_ = _args[13];
lean_object* v_R_1636_ = _args[14];
lean_object* v_a_1637_ = _args[15];
lean_object* v_b_1638_ = _args[16];
lean_object* v_c_1639_ = _args[17];
lean_object* v___y_1640_ = _args[18];
lean_object* v___y_1641_ = _args[19];
lean_object* v___y_1642_ = _args[20];
lean_object* v___y_1643_ = _args[21];
lean_object* v___y_1644_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1645_; uint8_t v_a_20026__boxed_1646_; lean_object* v_res_1647_; 
v_instImplicit_boxed_1645_ = lean_unbox(v_instImplicit_1626_);
v_a_20026__boxed_1646_ = lean_unbox(v_a_1634_);
v_res_1647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(v_upperBound_1622_, v_projDecls_1623_, v___x_1624_, v___x_1625_, v_instImplicit_boxed_1645_, v___x_1627_, v_params_1628_, v_self_1629_, v_a_1630_, v___x_1631_, v_n_1632_, v___x_1633_, v_a_20026__boxed_1646_, v_inst_1635_, v_R_1636_, v_a_1637_, v_b_1638_, v_c_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_projDecls_1623_);
lean_dec(v_upperBound_1622_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8(lean_object* v_declName_1648_, uint8_t v_s_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_1648_, v_s_1649_, v___y_1651_, v___y_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___boxed(lean_object* v_declName_1656_, lean_object* v_s_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v_s_boxed_1663_; lean_object* v_res_1664_; 
v_s_boxed_1663_ = lean_unbox(v_s_1657_);
v_res_1664_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8(v_declName_1656_, v_s_boxed_1663_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11(lean_object* v_00_u03b1_1665_, lean_object* v_x_1666_, uint8_t v_isExporting_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_1666_, v_isExporting_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_x_1675_, lean_object* v_isExporting_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_isExporting_boxed_1682_; lean_object* v_res_1683_; 
v_isExporting_boxed_1682_ = lean_unbox(v_isExporting_1676_);
v_res_1683_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11(v_00_u03b1_1674_, v_x_1675_, v_isExporting_boxed_1682_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1684_, uint8_t v_allowLevelAssignments_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1685_, v_k_1684_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1691_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1691_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1708_, lean_object* v_allowLevelAssignments_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1715_; lean_object* v_res_1716_; 
v_allowLevelAssignments_boxed_1715_ = lean_unbox(v_allowLevelAssignments_1709_);
v_res_1716_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1708_, v_allowLevelAssignments_boxed_1715_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1717_, lean_object* v_k_1718_, uint8_t v_allowLevelAssignments_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1718_, v_allowLevelAssignments_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1726_, lean_object* v_k_1727_, lean_object* v_allowLevelAssignments_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1734_; lean_object* v_res_1735_; 
v_allowLevelAssignments_boxed_1734_ = lean_unbox(v_allowLevelAssignments_1728_);
v_res_1735_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1726_, v_k_1727_, v_allowLevelAssignments_boxed_1734_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1736_, size_t v_sz_1737_, size_t v_i_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1738_, v_sz_1737_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1739_);
return v___x_1746_;
}
else
{
lean_object* v_snd_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1802_; 
v_snd_1747_ = lean_ctor_get(v_b_1739_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_b_1739_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_b_1739_, 0);
lean_dec(v_unused_1803_);
v___x_1749_ = v_b_1739_;
v_isShared_1750_ = v_isSharedCheck_1802_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_snd_1747_);
lean_dec(v_b_1739_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1802_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_array_1751_; lean_object* v_start_1752_; lean_object* v_stop_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_array_1751_ = lean_ctor_get(v_snd_1747_, 0);
v_start_1752_ = lean_ctor_get(v_snd_1747_, 1);
v_stop_1753_ = lean_ctor_get(v_snd_1747_, 2);
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_nat_dec_lt(v_start_1752_, v_stop_1753_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1754_);
v___x_1757_ = v___x_1749_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_snd_1747_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
else
{
lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1798_; 
lean_inc(v_stop_1753_);
lean_inc(v_start_1752_);
lean_inc_ref(v_array_1751_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_snd_1747_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1799_ = lean_ctor_get(v_snd_1747_, 2);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_snd_1747_, 1);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_snd_1747_, 0);
lean_dec(v_unused_1801_);
v___x_1761_ = v_snd_1747_;
v_isShared_1762_ = v_isSharedCheck_1798_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v_snd_1747_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1798_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v_a_1763_ = lean_array_uget_borrowed(v_as_1736_, v_i_1738_);
v___x_1764_ = lean_array_fget(v_array_1751_, v_start_1752_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_start_1752_, v___x_1765_);
lean_dec(v_start_1752_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1766_);
v___x_1768_ = v___x_1761_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_array_1751_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_stop_1753_);
v___x_1768_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; 
lean_inc(v_a_1763_);
v___x_1769_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1763_, v___x_1764_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1788_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1788_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1788_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_unbox(v_a_1770_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_a_1770_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1768_);
lean_ctor_set(v___x_1749_, 0, v___x_1775_);
v___x_1777_ = v___x_1749_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1768_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1777_);
v___x_1779_ = v___x_1772_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_object* v___x_1783_; 
lean_del_object(v___x_1772_);
lean_dec(v_a_1770_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1768_);
lean_ctor_set(v___x_1749_, 0, v___x_1754_);
v___x_1783_ = v___x_1749_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1768_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
size_t v___x_1784_; size_t v___x_1785_; 
v___x_1784_ = ((size_t)1ULL);
v___x_1785_ = lean_usize_add(v_i_1738_, v___x_1784_);
v_i_1738_ = v___x_1785_;
v_b_1739_ = v___x_1783_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___x_1768_);
lean_del_object(v___x_1749_);
v_a_1789_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1769_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1769_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1804_, lean_object* v_sz_1805_, lean_object* v_i_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
size_t v_sz_boxed_1813_; size_t v_i_boxed_1814_; lean_object* v_res_1815_; 
v_sz_boxed_1813_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1814_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1804_, v_sz_boxed_1813_, v_i_boxed_1814_, v_b_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_as_1804_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1816_, lean_object* v_params2_1817_, lean_object* v___x_1818_, lean_object* v_params1_1819_, uint8_t v___x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
if (v___x_1816_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v___x_1818_);
lean_dec_ref(v_params2_1817_);
v___x_1826_ = lean_box(v___x_1816_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; size_t v_sz_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = l_Array_toSubarray___redArg(v_params2_1817_, v___x_1828_, v___x_1818_);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___x_1829_);
v_sz_1832_ = lean_array_size(v_params1_1819_);
v___x_1833_ = ((size_t)0ULL);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1819_, v_sz_1832_, v___x_1833_, v___x_1831_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1848_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1848_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_fst_1839_; 
v_fst_1839_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_fst_1839_);
lean_dec(v_a_1835_);
if (lean_obj_tag(v_fst_1839_) == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(v___x_1820_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1846_; 
v_val_1844_ = lean_ctor_get(v_fst_1839_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_fst_1839_, 1);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v_val_1844_);
v___x_1846_ = v___x_1837_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_val_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1834_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1834_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1857_, lean_object* v_params2_1858_, lean_object* v___x_1859_, lean_object* v_params1_1860_, lean_object* v___x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v___x_2007__boxed_1867_; uint8_t v___x_2009__boxed_1868_; lean_object* v_res_1869_; 
v___x_2007__boxed_1867_ = lean_unbox(v___x_1857_);
v___x_2009__boxed_1868_ = lean_unbox(v___x_1861_);
v_res_1869_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1867_, v_params2_1858_, v___x_1859_, v_params1_1860_, v___x_2009__boxed_1868_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_params1_1860_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1870_, lean_object* v_params2_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___y_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1877_ = lean_array_get_size(v_params1_1870_);
v___x_1878_ = lean_array_get_size(v_params2_1871_);
v___x_1879_ = lean_nat_dec_eq(v___x_1877_, v___x_1878_);
v___x_1880_ = 1;
v___x_1881_ = lean_box(v___x_1879_);
v___x_1882_ = lean_box(v___x_1880_);
v___y_1883_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1883_, 0, v___x_1881_);
lean_closure_set(v___y_1883_, 1, v_params2_1871_);
lean_closure_set(v___y_1883_, 2, v___x_1878_);
lean_closure_set(v___y_1883_, 3, v_params1_1870_);
lean_closure_set(v___y_1883_, 4, v___x_1882_);
v___x_1884_ = 0;
v___x_1885_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1883_, v___x_1884_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1886_, lean_object* v_params2_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1886_, v_params2_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v_env_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_st_ref_get(v___y_1895_);
v_env_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_ref(v_env_1898_);
lean_dec(v___x_1897_);
v___x_1899_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1898_, v_declName_1894_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1901_, v___y_1902_);
lean_dec(v___y_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1905_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1919_; lean_object* v_dummy_1920_; 
v___x_1919_ = lean_box(0);
v_dummy_1920_ = l_Lean_Expr_sort___override(v___x_1919_);
return v_dummy_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1921_, lean_object* v_induct_1922_, lean_object* v_params_1923_, lean_object* v_idx_1924_, lean_object* v_e_1925_, lean_object* v_x_x3f_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
if (lean_obj_tag(v_e_1925_) == 11)
{
lean_object* v_typeName_1938_; lean_object* v_idx_1939_; lean_object* v_struct_1940_; uint8_t v___x_1987_; 
v_typeName_1938_ = lean_ctor_get(v_e_1925_, 0);
v_idx_1939_ = lean_ctor_get(v_e_1925_, 1);
v_struct_1940_ = lean_ctor_get(v_e_1925_, 2);
lean_inc_ref(v_struct_1940_);
v___x_1987_ = lean_nat_dec_eq(v_idx_1939_, v_idx_1924_);
if (v___x_1987_ == 0)
{
lean_dec_ref(v_struct_1940_);
lean_dec_ref_known(v_e_1925_, 3);
lean_dec_ref(v_params_1923_);
goto v___jp_1935_;
}
else
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_name_eq(v_induct_1922_, v_typeName_1938_);
if (v___x_1988_ == 0)
{
lean_dec_ref(v_struct_1940_);
lean_dec_ref_known(v_e_1925_, 3);
lean_dec_ref(v_params_1923_);
goto v___jp_1935_;
}
else
{
if (lean_obj_tag(v_x_x3f_1926_) == 0)
{
goto v___jp_1941_;
}
else
{
lean_object* v_val_1989_; uint8_t v___x_1990_; 
v_val_1989_ = lean_ctor_get(v_x_x3f_1926_, 0);
v___x_1990_ = lean_expr_eqv(v_val_1989_, v_struct_1940_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v_struct_1940_);
lean_dec_ref_known(v_e_1925_, 3);
lean_dec_ref(v_params_1923_);
goto v___jp_1935_;
}
else
{
goto v___jp_1941_;
}
}
}
}
v___jp_1941_:
{
lean_object* v___x_1942_; 
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_1942_ = lean_infer_type(v_e_1925_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
lean_inc(v_a_1930_);
lean_inc_ref(v_a_1929_);
lean_inc(v_a_1928_);
lean_inc_ref(v_a_1927_);
v___x_1944_ = lean_whnf(v_a_1943_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v_dummy_1946_; lean_object* v_nargs_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_dummy_1946_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1947_ = l_Lean_Expr_getAppNumArgs(v_a_1945_);
lean_inc(v_nargs_1947_);
v___x_1948_ = lean_mk_array(v_nargs_1947_, v_dummy_1946_);
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = lean_nat_sub(v_nargs_1947_, v___x_1949_);
lean_dec(v_nargs_1947_);
v___x_1951_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1945_, v___x_1948_, v___x_1950_);
v___x_1952_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1923_, v___x_1951_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1962_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1962_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1962_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_unbox(v_a_1953_);
lean_dec(v_a_1953_);
if (v___x_1957_ == 0)
{
lean_del_object(v___x_1955_);
lean_dec_ref(v_struct_1940_);
goto v___jp_1935_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_struct_1940_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1958_);
v___x_1960_ = v___x_1955_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
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
lean_dec_ref(v_struct_1940_);
v_a_1963_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1952_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1952_);
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
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v_struct_1940_);
lean_dec_ref(v_params_1923_);
v_a_1971_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1944_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1944_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_struct_1940_);
lean_dec_ref(v_params_1923_);
v_a_1979_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1942_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1942_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
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
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Expr_getAppFn(v_e_1925_);
if (lean_obj_tag(v___x_1991_) == 4)
{
lean_object* v_declName_1992_; lean_object* v___x_1993_; lean_object* v_a_1994_; 
v_declName_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_declName_1992_);
lean_dec_ref_known(v___x_1991_, 2);
v___x_1993_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1992_, v_a_1930_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref(v___x_1993_);
if (lean_obj_tag(v_a_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2039_; 
v_val_1995_ = lean_ctor_get(v_a_1994_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_1997_ = v_a_1994_;
v_isShared_1998_ = v_isSharedCheck_2039_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v_a_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2039_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_ctorName_1999_; lean_object* v_numParams_2000_; lean_object* v_i_2001_; uint8_t v___x_2002_; 
v_ctorName_1999_ = lean_ctor_get(v_val_1995_, 0);
lean_inc(v_ctorName_1999_);
v_numParams_2000_ = lean_ctor_get(v_val_1995_, 1);
lean_inc(v_numParams_2000_);
v_i_2001_ = lean_ctor_get(v_val_1995_, 2);
lean_inc(v_i_2001_);
lean_dec(v_val_1995_);
v___x_2002_ = lean_name_eq(v_ctorName_1999_, v_ctor_1921_);
lean_dec(v_ctorName_1999_);
if (v___x_2002_ == 0)
{
lean_dec(v_i_2001_);
lean_dec(v_numParams_2000_);
lean_del_object(v___x_1997_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
else
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_nat_dec_eq(v_i_2001_, v_idx_1924_);
lean_dec(v_i_2001_);
if (v___x_2003_ == 0)
{
lean_dec(v_numParams_2000_);
lean_del_object(v___x_1997_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2004_ = l_Lean_Expr_getAppNumArgs(v_e_1925_);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_nat_add(v_numParams_2000_, v___x_2005_);
lean_dec(v_numParams_2000_);
v___x_2007_ = lean_nat_dec_eq(v___x_2004_, v___x_2006_);
lean_dec(v___x_2006_);
lean_dec(v___x_2004_);
if (v___x_2007_ == 0)
{
lean_del_object(v___x_1997_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Expr_appArg_x21(v_e_1925_);
if (lean_obj_tag(v_x_x3f_1926_) == 0)
{
goto v___jp_2009_;
}
else
{
lean_object* v_val_2037_; uint8_t v___x_2038_; 
v_val_2037_ = lean_ctor_get(v_x_x3f_1926_, 0);
v___x_2038_ = lean_expr_eqv(v_val_2037_, v___x_2008_);
if (v___x_2038_ == 0)
{
lean_dec_ref(v___x_2008_);
lean_del_object(v___x_1997_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
else
{
goto v___jp_2009_;
}
}
v___jp_2009_:
{
lean_object* v___x_2010_; lean_object* v_dummy_2011_; lean_object* v_nargs_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2010_ = l_Lean_Expr_appFn_x21(v_e_1925_);
lean_dec_ref(v_e_1925_);
v_dummy_2011_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2012_ = l_Lean_Expr_getAppNumArgs(v___x_2010_);
lean_inc(v_nargs_2012_);
v___x_2013_ = lean_mk_array(v_nargs_2012_, v_dummy_2011_);
v___x_2014_ = lean_nat_sub(v_nargs_2012_, v___x_2005_);
lean_dec(v_nargs_2012_);
v___x_2015_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2010_, v___x_2013_, v___x_2014_);
v___x_2016_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1923_, v___x_2015_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2028_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_unbox(v_a_2017_);
lean_dec(v_a_2017_);
if (v___x_2021_ == 0)
{
lean_del_object(v___x_2019_);
lean_dec_ref(v___x_2008_);
lean_del_object(v___x_1997_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_2023_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2008_);
v___x_2023_ = v___x_1997_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2008_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v___x_2008_);
lean_del_object(v___x_1997_);
v_a_2029_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2016_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2016_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
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
lean_dec(v_a_1994_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
}
else
{
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_e_1925_);
lean_dec_ref(v_params_1923_);
goto v___jp_1932_;
}
}
v___jp_1932_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
return v___x_1934_;
}
v___jp_1935_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2040_, lean_object* v_induct_2041_, lean_object* v_params_2042_, lean_object* v_idx_2043_, lean_object* v_e_2044_, lean_object* v_x_x3f_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2040_, v_induct_2041_, v_params_2042_, v_idx_2043_, v_e_2044_, v_x_x3f_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_x_x3f_2045_);
lean_dec(v_idx_2043_);
lean_dec(v_induct_2041_);
lean_dec(v_ctor_2040_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v_env_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2058_ = lean_st_ref_get(v___y_2056_);
v_env_2062_ = lean_ctor_get(v___x_2058_, 0);
lean_inc_ref(v_env_2062_);
lean_dec(v___x_2058_);
v___x_2063_ = 0;
v___x_2064_ = l_Lean_Environment_findAsync_x3f(v_env_2062_, v_constName_2052_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2084_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2084_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_val_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2084_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
uint8_t v_kind_2069_; 
v_kind_2069_ = lean_ctor_get_uint8(v_val_2065_, sizeof(void*)*3);
if (v_kind_2069_ == 6)
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2065_);
if (lean_obj_tag(v___x_2070_) == 6)
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2081_; 
v_val_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2081_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v_val_2071_);
v___x_2076_ = v___x_2067_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_val_2071_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2078_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___x_2070_);
lean_del_object(v___x_2067_);
v___x_2082_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2083_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2082_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
return v___x_2083_;
}
}
else
{
lean_del_object(v___x_2067_);
lean_dec(v_val_2065_);
goto v___jp_2059_;
}
}
}
else
{
lean_dec(v___x_2064_);
goto v___jp_2059_;
}
v___jp_2059_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v_declName_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v_a_2106_, lean_object* v_val_2107_, lean_object* v_a_2108_, lean_object* v_b_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_nat_dec_lt(v_a_2108_, v_upperBound_2100_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_dec(v_a_2108_);
lean_dec_ref(v___x_2105_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_b_2109_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref(v_b_2109_);
v___x_2117_ = l_Lean_instInhabitedExpr;
v___x_2118_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2119_ = lean_nat_add(v___x_2101_, v_a_2108_);
v___x_2120_ = lean_array_get_borrowed(v___x_2117_, v___x_2102_, v___x_2119_);
lean_dec(v___x_2119_);
lean_inc(v___x_2120_);
lean_inc_ref(v___x_2105_);
v___x_2121_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2103_, v___x_2104_, v___x_2105_, v_a_2108_, v___x_2120_, v_a_2106_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2139_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2139_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2139_;
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
v___x_2127_ = lean_expr_eqv(v_val_2126_, v_val_2107_);
lean_dec(v_val_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec(v_a_2108_);
lean_dec_ref(v___x_2105_);
v___x_2128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
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
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2124_);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_add(v_a_2108_, v___x_2132_);
lean_dec(v_a_2108_);
v_a_2108_ = v___x_2133_;
v_b_2109_ = v___x_2118_;
goto _start;
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec(v_a_2122_);
lean_dec(v_a_2108_);
lean_dec_ref(v___x_2105_);
v___x_2135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2135_);
v___x_2137_ = v___x_2124_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2108_);
lean_dec_ref(v___x_2105_);
v_a_2140_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2121_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2121_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_declName_2151_, lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v_a_2154_, lean_object* v_val_2155_, lean_object* v_a_2156_, lean_object* v_b_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2148_, v___x_2149_, v___x_2150_, v_declName_2151_, v___x_2152_, v___x_2153_, v_a_2154_, v_val_2155_, v_a_2156_, v_b_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec_ref(v_val_2155_);
lean_dec(v_a_2154_);
lean_dec(v___x_2152_);
lean_dec(v_declName_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
lean_dec(v_upperBound_2148_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2164_, lean_object* v_p_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_Expr_getAppFn(v_e_2164_);
if (lean_obj_tag(v___x_2171_) == 4)
{
lean_object* v_declName_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_declName_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc_n(v_declName_2172_, 2);
lean_dec_ref_known(v___x_2171_, 2);
v___x_2173_ = l_Lean_instInhabitedExpr;
v___x_2174_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2172_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2246_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2246_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2246_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2243_; 
v_val_2184_ = lean_ctor_get(v_a_2175_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2186_ = v_a_2175_;
v_isShared_2187_ = v_isSharedCheck_2243_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_val_2184_);
lean_dec(v_a_2175_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2243_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_induct_2188_; lean_object* v_numParams_2189_; lean_object* v_numFields_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_induct_2188_ = lean_ctor_get(v_val_2184_, 1);
lean_inc_n(v_induct_2188_, 2);
v_numParams_2189_ = lean_ctor_get(v_val_2184_, 3);
lean_inc(v_numParams_2189_);
v_numFields_2190_ = lean_ctor_get(v_val_2184_, 4);
lean_inc(v_numFields_2190_);
lean_dec(v_val_2184_);
v___x_2191_ = lean_apply_1(v_p_2165_, v_induct_2188_);
v___x_2192_ = lean_unbox(v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_numFields_2190_);
lean_dec(v_numParams_2189_);
lean_dec(v_induct_2188_);
lean_del_object(v___x_2177_);
lean_dec(v_declName_2172_);
lean_dec_ref(v_e_2164_);
v___x_2193_ = lean_box(0);
if (v_isShared_2187_ == 0)
{
lean_ctor_set_tag(v___x_2186_, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2193_);
v___x_2195_ = v___x_2186_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
lean_del_object(v___x_2186_);
v___x_2197_ = lean_unsigned_to_nat(0u);
v___x_2198_ = lean_nat_dec_lt(v___x_2197_, v_numFields_2190_);
if (v___x_2198_ == 0)
{
lean_dec(v_numFields_2190_);
lean_dec(v_numParams_2189_);
lean_dec(v_induct_2188_);
lean_dec(v_declName_2172_);
lean_dec_ref(v_e_2164_);
goto v___jp_2179_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = l_Lean_Expr_getAppNumArgs(v_e_2164_);
v___x_2200_ = lean_nat_add(v_numParams_2189_, v_numFields_2190_);
v___x_2201_ = lean_nat_dec_eq(v___x_2199_, v___x_2200_);
lean_dec(v___x_2200_);
if (v___x_2201_ == 0)
{
lean_dec(v___x_2199_);
lean_dec(v_numFields_2190_);
lean_dec(v_numParams_2189_);
lean_dec(v_induct_2188_);
lean_dec(v_declName_2172_);
lean_dec_ref(v_e_2164_);
goto v___jp_2179_;
}
else
{
lean_object* v_dummy_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_del_object(v___x_2177_);
v_dummy_2202_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2199_);
v___x_2203_ = lean_mk_array(v___x_2199_, v_dummy_2202_);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_nat_sub(v___x_2199_, v___x_2204_);
lean_dec(v___x_2199_);
v___x_2206_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2164_, v___x_2203_, v___x_2205_);
lean_inc(v_numParams_2189_);
v___x_2207_ = l_Array_extract___redArg(v___x_2206_, v___x_2197_, v_numParams_2189_);
v___x_2208_ = lean_array_get_borrowed(v___x_2173_, v___x_2206_, v_numParams_2189_);
v___x_2209_ = lean_box(0);
lean_inc(v___x_2208_);
lean_inc_ref(v___x_2207_);
v___x_2210_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2172_, v_induct_2188_, v___x_2207_, v___x_2197_, v___x_2208_, v___x_2209_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2242_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2242_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2242_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
if (lean_obj_tag(v_a_2211_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_del_object(v___x_2213_);
v_val_2215_ = lean_ctor_get(v_a_2211_, 0);
v___x_2216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2190_, v_numParams_2189_, v___x_2206_, v_declName_2172_, v_induct_2188_, v___x_2207_, v_a_2211_, v_val_2215_, v___x_2204_, v___x_2216_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_induct_2188_);
lean_dec(v_declName_2172_);
lean_dec_ref(v___x_2206_);
lean_dec(v_numParams_2189_);
lean_dec(v_numFields_2190_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2230_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2230_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2230_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_fst_2222_; 
v_fst_2222_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_fst_2222_);
lean_dec(v_a_2218_);
if (lean_obj_tag(v_fst_2222_) == 0)
{
lean_object* v___x_2224_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_a_2211_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2211_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
else
{
lean_object* v_val_2226_; lean_object* v___x_2228_; 
lean_dec_ref_known(v_a_2211_, 1);
v_val_2226_ = lean_ctor_get(v_fst_2222_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v_fst_2222_, 1);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v_val_2226_);
v___x_2228_ = v___x_2220_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_val_2226_);
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
lean_dec_ref_known(v_a_2211_, 1);
v_a_2231_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2217_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2217_);
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
lean_object* v___x_2240_; 
lean_dec(v_a_2211_);
lean_dec_ref(v___x_2207_);
lean_dec_ref(v___x_2206_);
lean_dec(v_numFields_2190_);
lean_dec(v_numParams_2189_);
lean_dec(v_induct_2188_);
lean_dec(v_declName_2172_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2209_);
v___x_2240_ = v___x_2213_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2209_);
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
lean_dec_ref(v___x_2207_);
lean_dec_ref(v___x_2206_);
lean_dec(v_numFields_2190_);
lean_dec(v_numParams_2189_);
lean_dec(v_induct_2188_);
lean_dec(v_declName_2172_);
return v___x_2210_;
}
}
}
}
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_del_object(v___x_2177_);
lean_dec(v_a_2175_);
lean_dec(v_declName_2172_);
lean_dec_ref(v_p_2165_);
lean_dec_ref(v_e_2164_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
v___jp_2179_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2180_);
v___x_2182_ = v___x_2177_;
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
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_declName_2172_);
lean_dec_ref(v_p_2165_);
lean_dec_ref(v_e_2164_);
v_a_2247_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2174_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2174_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_p_2165_);
lean_dec_ref(v_e_2164_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2257_, lean_object* v_p_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Meta_etaStruct_x3f(v_e_2257_, v_p_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2265_, lean_object* v___x_2266_, lean_object* v___x_2267_, lean_object* v_declName_2268_, lean_object* v___x_2269_, lean_object* v___x_2270_, lean_object* v_a_2271_, lean_object* v_val_2272_, lean_object* v_inst_2273_, lean_object* v_R_2274_, lean_object* v_a_2275_, lean_object* v_b_2276_, lean_object* v_c_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2265_, v___x_2266_, v___x_2267_, v_declName_2268_, v___x_2269_, v___x_2270_, v_a_2271_, v_val_2272_, v_a_2275_, v_b_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2284_ = _args[0];
lean_object* v___x_2285_ = _args[1];
lean_object* v___x_2286_ = _args[2];
lean_object* v_declName_2287_ = _args[3];
lean_object* v___x_2288_ = _args[4];
lean_object* v___x_2289_ = _args[5];
lean_object* v_a_2290_ = _args[6];
lean_object* v_val_2291_ = _args[7];
lean_object* v_inst_2292_ = _args[8];
lean_object* v_R_2293_ = _args[9];
lean_object* v_a_2294_ = _args[10];
lean_object* v_b_2295_ = _args[11];
lean_object* v_c_2296_ = _args[12];
lean_object* v___y_2297_ = _args[13];
lean_object* v___y_2298_ = _args[14];
lean_object* v___y_2299_ = _args[15];
lean_object* v___y_2300_ = _args[16];
lean_object* v___y_2301_ = _args[17];
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2284_, v___x_2285_, v___x_2286_, v_declName_2287_, v___x_2288_, v___x_2289_, v_a_2290_, v_val_2291_, v_inst_2292_, v_R_2293_, v_a_2294_, v_b_2295_, v_c_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_val_2291_);
lean_dec(v_a_2290_);
lean_dec(v___x_2288_);
lean_dec(v_declName_2287_);
lean_dec_ref(v___x_2286_);
lean_dec(v___x_2285_);
lean_dec(v_upperBound_2284_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = l_Lean_Expr_hasMVar(v_e_2303_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_e_2303_);
return v___x_2307_;
}
else
{
lean_object* v___x_2308_; lean_object* v_mctx_2309_; lean_object* v___x_2310_; lean_object* v_fst_2311_; lean_object* v_snd_2312_; lean_object* v___x_2313_; lean_object* v_cache_2314_; lean_object* v_zetaDeltaFVarIds_2315_; lean_object* v_postponed_2316_; lean_object* v_diag_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2326_; 
v___x_2308_ = lean_st_ref_get(v___y_2304_);
v_mctx_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_ref(v_mctx_2309_);
lean_dec(v___x_2308_);
v___x_2310_ = l_Lean_instantiateMVarsCore(v_mctx_2309_, v_e_2303_);
v_fst_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_fst_2311_);
v_snd_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2312_);
lean_dec_ref(v___x_2310_);
v___x_2313_ = lean_st_ref_take(v___y_2304_);
v_cache_2314_ = lean_ctor_get(v___x_2313_, 1);
v_zetaDeltaFVarIds_2315_ = lean_ctor_get(v___x_2313_, 2);
v_postponed_2316_ = lean_ctor_get(v___x_2313_, 3);
v_diag_2317_ = lean_ctor_get(v___x_2313_, 4);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v___x_2313_, 0);
lean_dec(v_unused_2327_);
v___x_2319_ = v___x_2313_;
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_diag_2317_);
lean_inc(v_postponed_2316_);
lean_inc(v_zetaDeltaFVarIds_2315_);
lean_inc(v_cache_2314_);
lean_dec(v___x_2313_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_snd_2312_);
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_snd_2312_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_cache_2314_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_zetaDeltaFVarIds_2315_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_postponed_2316_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_diag_2317_);
v___x_2322_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_st_ref_put(v___y_2304_, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_fst_2311_);
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2328_, v___y_2329_);
lean_dec(v___y_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2332_, v___y_2334_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_x_2356_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2363_, lean_object* v_e_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_etaStruct_x3f(v_e_2364_, v_p_2363_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2390_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2390_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2390_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
if (lean_obj_tag(v_a_2371_) == 1)
{
lean_object* v_val_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2385_; 
v_val_2375_ = lean_ctor_get(v_a_2371_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_a_2371_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2377_ = v_a_2371_;
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_val_2375_);
lean_dec(v_a_2371_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 0);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_val_2375_);
v___x_2380_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2382_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2380_);
v___x_2382_ = v___x_2373_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_dec(v_a_2371_);
v___x_2386_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2386_);
v___x_2388_ = v___x_2373_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_a_2391_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2370_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2370_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2399_, lean_object* v_e_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2399_, v_e_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_apply_1(v_x_2408_, lean_box(0));
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2416_, v_x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2424_, lean_object* v_b_2425_, lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
lean_dec(v_b_2425_);
lean_dec_ref(v_a_2424_);
return v_x_2426_;
}
else
{
lean_object* v_key_2427_; lean_object* v_value_2428_; lean_object* v_tail_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2441_; 
v_key_2427_ = lean_ctor_get(v_x_2426_, 0);
v_value_2428_ = lean_ctor_get(v_x_2426_, 1);
v_tail_2429_ = lean_ctor_get(v_x_2426_, 2);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2431_ = v_x_2426_;
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_tail_2429_);
lean_inc(v_value_2428_);
lean_inc(v_key_2427_);
lean_dec(v_x_2426_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2441_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
uint8_t v___x_2433_; 
v___x_2433_ = l_Lean_ExprStructEq_beq(v_key_2427_, v_a_2424_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2424_, v_b_2425_, v_tail_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 2, v___x_2434_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_key_2427_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_value_2428_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
else
{
lean_object* v___x_2439_; 
lean_dec(v_value_2428_);
lean_dec(v_key_2427_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v_b_2425_);
lean_ctor_set(v___x_2431_, 0, v_a_2424_);
v___x_2439_ = v___x_2431_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2424_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_b_2425_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_tail_2429_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
return v_x_2442_;
}
else
{
lean_object* v_key_2444_; lean_object* v_value_2445_; lean_object* v_tail_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2469_; 
v_key_2444_ = lean_ctor_get(v_x_2443_, 0);
v_value_2445_ = lean_ctor_get(v_x_2443_, 1);
v_tail_2446_ = lean_ctor_get(v_x_2443_, 2);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2448_ = v_x_2443_;
v_isShared_2449_ = v_isSharedCheck_2469_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_tail_2446_);
lean_inc(v_value_2445_);
lean_inc(v_key_2444_);
lean_dec(v_x_2443_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2469_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v___x_2453_; uint64_t v_fold_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; uint64_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2450_ = lean_array_get_size(v_x_2442_);
v___x_2451_ = l_Lean_ExprStructEq_hash(v_key_2444_);
v___x_2452_ = 32ULL;
v___x_2453_ = lean_uint64_shift_right(v___x_2451_, v___x_2452_);
v_fold_2454_ = lean_uint64_xor(v___x_2451_, v___x_2453_);
v___x_2455_ = 16ULL;
v___x_2456_ = lean_uint64_shift_right(v_fold_2454_, v___x_2455_);
v___x_2457_ = lean_uint64_xor(v_fold_2454_, v___x_2456_);
v___x_2458_ = lean_uint64_to_usize(v___x_2457_);
v___x_2459_ = lean_usize_of_nat(v___x_2450_);
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_sub(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_usize_land(v___x_2458_, v___x_2461_);
v___x_2463_ = lean_array_uget_borrowed(v_x_2442_, v___x_2462_);
lean_inc(v___x_2463_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 2, v___x_2463_);
v___x_2465_ = v___x_2448_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_key_2444_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_value_2445_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
v___x_2466_ = lean_array_uset(v_x_2442_, v___x_2462_, v___x_2465_);
v_x_2442_ = v___x_2466_;
v_x_2443_ = v_tail_2446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2470_, lean_object* v_source_2471_, lean_object* v_target_2472_){
_start:
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = lean_array_get_size(v_source_2471_);
v___x_2474_ = lean_nat_dec_lt(v_i_2470_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_dec_ref(v_source_2471_);
lean_dec(v_i_2470_);
return v_target_2472_;
}
else
{
lean_object* v_es_2475_; lean_object* v___x_2476_; lean_object* v_source_2477_; lean_object* v_target_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_es_2475_ = lean_array_fget(v_source_2471_, v_i_2470_);
v___x_2476_ = lean_box(0);
v_source_2477_ = lean_array_fset(v_source_2471_, v_i_2470_, v___x_2476_);
v_target_2478_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2472_, v_es_2475_);
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_i_2470_, v___x_2479_);
lean_dec(v_i_2470_);
v_i_2470_ = v___x_2480_;
v_source_2471_ = v_source_2477_;
v_target_2472_ = v_target_2478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_nbuckets_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2483_ = lean_array_get_size(v_data_2482_);
v___x_2484_ = lean_unsigned_to_nat(2u);
v_nbuckets_2485_ = lean_nat_mul(v___x_2483_, v___x_2484_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_mk_array(v_nbuckets_2485_, v___x_2487_);
v___x_2489_ = lean_array_propagate_mark(v_data_2482_, v___x_2488_);
v___x_2490_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2486_, v_data_2482_, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2491_, lean_object* v_x_2492_){
_start:
{
if (lean_obj_tag(v_x_2492_) == 0)
{
uint8_t v___x_2493_; 
v___x_2493_ = 0;
return v___x_2493_;
}
else
{
lean_object* v_key_2494_; lean_object* v_tail_2495_; uint8_t v___x_2496_; 
v_key_2494_ = lean_ctor_get(v_x_2492_, 0);
v_tail_2495_ = lean_ctor_get(v_x_2492_, 2);
v___x_2496_ = l_Lean_ExprStructEq_beq(v_key_2494_, v_a_2491_);
if (v___x_2496_ == 0)
{
v_x_2492_ = v_tail_2495_;
goto _start;
}
else
{
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2498_, lean_object* v_x_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2498_, v_x_2499_);
lean_dec(v_x_2499_);
lean_dec_ref(v_a_2498_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v_size_2505_; lean_object* v_buckets_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2549_; 
v_size_2505_ = lean_ctor_get(v_m_2502_, 0);
v_buckets_2506_ = lean_ctor_get(v_m_2502_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_m_2502_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2508_ = v_m_2502_;
v_isShared_2509_ = v_isSharedCheck_2549_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_buckets_2506_);
lean_inc(v_size_2505_);
lean_dec(v_m_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2549_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; uint64_t v___x_2513_; uint64_t v_fold_2514_; uint64_t v___x_2515_; uint64_t v___x_2516_; uint64_t v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; size_t v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; lean_object* v_bkt_2523_; uint8_t v___x_2524_; 
v___x_2510_ = lean_array_get_size(v_buckets_2506_);
v___x_2511_ = l_Lean_ExprStructEq_hash(v_a_2503_);
v___x_2512_ = 32ULL;
v___x_2513_ = lean_uint64_shift_right(v___x_2511_, v___x_2512_);
v_fold_2514_ = lean_uint64_xor(v___x_2511_, v___x_2513_);
v___x_2515_ = 16ULL;
v___x_2516_ = lean_uint64_shift_right(v_fold_2514_, v___x_2515_);
v___x_2517_ = lean_uint64_xor(v_fold_2514_, v___x_2516_);
v___x_2518_ = lean_uint64_to_usize(v___x_2517_);
v___x_2519_ = lean_usize_of_nat(v___x_2510_);
v___x_2520_ = ((size_t)1ULL);
v___x_2521_ = lean_usize_sub(v___x_2519_, v___x_2520_);
v___x_2522_ = lean_usize_land(v___x_2518_, v___x_2521_);
v_bkt_2523_ = lean_array_uget_borrowed(v_buckets_2506_, v___x_2522_);
v___x_2524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2503_, v_bkt_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; lean_object* v_size_x27_2526_; lean_object* v___x_2527_; lean_object* v_buckets_x27_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2525_ = lean_unsigned_to_nat(1u);
v_size_x27_2526_ = lean_nat_add(v_size_2505_, v___x_2525_);
lean_dec(v_size_2505_);
lean_inc(v_bkt_2523_);
v___x_2527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2527_, 0, v_a_2503_);
lean_ctor_set(v___x_2527_, 1, v_b_2504_);
lean_ctor_set(v___x_2527_, 2, v_bkt_2523_);
v_buckets_x27_2528_ = lean_array_uset(v_buckets_2506_, v___x_2522_, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(4u);
v___x_2530_ = lean_nat_mul(v_size_x27_2526_, v___x_2529_);
v___x_2531_ = lean_unsigned_to_nat(3u);
v___x_2532_ = lean_nat_div(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_array_get_size(v_buckets_x27_2528_);
v___x_2534_ = lean_nat_dec_le(v___x_2532_, v___x_2533_);
lean_dec(v___x_2532_);
if (v___x_2534_ == 0)
{
lean_object* v_val_2535_; lean_object* v___x_2537_; 
v_val_2535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2528_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v_val_2535_);
lean_ctor_set(v___x_2508_, 0, v_size_x27_2526_);
v___x_2537_ = v___x_2508_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_size_x27_2526_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_val_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
else
{
lean_object* v___x_2540_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v_buckets_x27_2528_);
lean_ctor_set(v___x_2508_, 0, v_size_x27_2526_);
v___x_2540_ = v___x_2508_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_size_x27_2526_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_buckets_x27_2528_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v___x_2542_; lean_object* v_buckets_x27_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_inc(v_bkt_2523_);
v___x_2542_ = lean_box(0);
v_buckets_x27_2543_ = lean_array_uset(v_buckets_2506_, v___x_2522_, v___x_2542_);
v___x_2544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2503_, v_b_2504_, v_bkt_2523_);
v___x_2545_ = lean_array_uset(v_buckets_x27_2543_, v___x_2522_, v___x_2544_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2545_);
v___x_2547_ = v___x_2508_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_size_2505_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2550_, lean_object* v_e_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2554_ = lean_st_ref_take(v_a_2550_);
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2554_, v_e_2551_, v_a_2552_);
v___x_2557_ = lean_st_ref_put(v_a_2550_, v___x_2556_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2558_, lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2558_, v_e_2559_, v_a_2560_);
lean_dec(v_a_2558_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_apply_1(v_x_2564_, lean_box(0));
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2572_, v_x_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2580_, lean_object* v_x_2581_){
_start:
{
if (lean_obj_tag(v_x_2581_) == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_box(0);
return v___x_2582_;
}
else
{
lean_object* v_key_2583_; lean_object* v_value_2584_; lean_object* v_tail_2585_; uint8_t v___x_2586_; 
v_key_2583_ = lean_ctor_get(v_x_2581_, 0);
v_value_2584_ = lean_ctor_get(v_x_2581_, 1);
v_tail_2585_ = lean_ctor_get(v_x_2581_, 2);
v___x_2586_ = l_Lean_ExprStructEq_beq(v_key_2583_, v_a_2580_);
if (v___x_2586_ == 0)
{
v_x_2581_ = v_tail_2585_;
goto _start;
}
else
{
lean_object* v___x_2588_; 
lean_inc(v_value_2584_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_value_2584_);
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2589_, v_x_2590_);
lean_dec(v_x_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_buckets_2594_; lean_object* v___x_2595_; uint64_t v___x_2596_; uint64_t v___x_2597_; uint64_t v___x_2598_; uint64_t v_fold_2599_; uint64_t v___x_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_buckets_2594_ = lean_ctor_get(v_m_2592_, 1);
v___x_2595_ = lean_array_get_size(v_buckets_2594_);
v___x_2596_ = l_Lean_ExprStructEq_hash(v_a_2593_);
v___x_2597_ = 32ULL;
v___x_2598_ = lean_uint64_shift_right(v___x_2596_, v___x_2597_);
v_fold_2599_ = lean_uint64_xor(v___x_2596_, v___x_2598_);
v___x_2600_ = 16ULL;
v___x_2601_ = lean_uint64_shift_right(v_fold_2599_, v___x_2600_);
v___x_2602_ = lean_uint64_xor(v_fold_2599_, v___x_2601_);
v___x_2603_ = lean_uint64_to_usize(v___x_2602_);
v___x_2604_ = lean_usize_of_nat(v___x_2595_);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_sub(v___x_2604_, v___x_2605_);
v___x_2607_ = lean_usize_land(v___x_2603_, v___x_2606_);
v___x_2608_ = lean_array_uget_borrowed(v_buckets_2594_, v___x_2607_);
v___x_2609_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2593_, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2610_, v_a_2611_);
lean_dec_ref(v_a_2611_);
lean_dec_ref(v_m_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2613_, lean_object* v___y_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; 
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___y_2614_);
v___x_2621_ = lean_apply_7(v_k_2613_, v_b_2615_, v___y_2614_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, lean_box(0));
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2622_, lean_object* v___y_2623_, lean_object* v_b_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2622_, v___y_2623_, v_b_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2623_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2631_, uint8_t v_bi_2632_, lean_object* v_type_2633_, lean_object* v_k_2634_, uint8_t v_kind_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___f_2642_; lean_object* v___x_2643_; 
lean_inc(v___y_2636_);
v___f_2642_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2642_, 0, v_k_2634_);
lean_closure_set(v___f_2642_, 1, v___y_2636_);
v___x_2643_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2631_, v_bi_2632_, v_type_2633_, v___f_2642_, v_kind_2635_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2643_) == 0)
{
return v___x_2643_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2652_, lean_object* v_bi_2653_, lean_object* v_type_2654_, lean_object* v_k_2655_, lean_object* v_kind_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_bi_boxed_2663_; uint8_t v_kind_boxed_2664_; lean_object* v_res_2665_; 
v_bi_boxed_2663_ = lean_unbox(v_bi_2653_);
v_kind_boxed_2664_ = lean_unbox(v_kind_2656_);
v_res_2665_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2652_, v_bi_boxed_2663_, v_type_2654_, v_k_2655_, v_kind_boxed_2664_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2666_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2680_, lean_object* v_type_2681_, lean_object* v_val_2682_, lean_object* v_k_2683_, uint8_t v_nondep_2684_, uint8_t v_kind_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; 
lean_inc(v___y_2686_);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2692_, 0, v_k_2683_);
lean_closure_set(v___f_2692_, 1, v___y_2686_);
v___x_2693_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2680_, v_type_2681_, v_val_2682_, v___f_2692_, v_nondep_2684_, v_kind_2685_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2693_) == 0)
{
return v___x_2693_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2702_, lean_object* v_type_2703_, lean_object* v_val_2704_, lean_object* v_k_2705_, lean_object* v_nondep_2706_, lean_object* v_kind_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
uint8_t v_nondep_boxed_2714_; uint8_t v_kind_boxed_2715_; lean_object* v_res_2716_; 
v_nondep_boxed_2714_ = lean_unbox(v_nondep_2706_);
v_kind_boxed_2715_ = lean_unbox(v_kind_2707_);
v_res_2716_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2702_, v_type_2703_, v_val_2704_, v_k_2705_, v_nondep_boxed_2714_, v_kind_boxed_2715_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
return v_res_2716_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = l_Lean_maxRecDepthErrorMessage;
v___x_2723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2725_ = l_Lean_MessageData_ofFormat(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2727_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2728_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___x_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2729_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_ref_2729_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___y_2745_; lean_object* v_toCold_2754_; lean_object* v_currRecDepth_2755_; lean_object* v_ref_2756_; uint16_t v_optionFlags_2757_; uint8_t v_suppressElabErrors_2758_; uint8_t v_checkDeprecated_2759_; uint8_t v_isRecordingDeps_2760_; lean_object* v_maxRecDepth_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_toCold_2754_ = lean_ctor_get(v___y_2741_, 0);
v_currRecDepth_2755_ = lean_ctor_get(v___y_2741_, 1);
v_ref_2756_ = lean_ctor_get(v___y_2741_, 2);
v_optionFlags_2757_ = lean_ctor_get_uint16(v___y_2741_, sizeof(void*)*3);
v_suppressElabErrors_2758_ = lean_ctor_get_uint8(v___y_2741_, sizeof(void*)*3 + 2);
v_checkDeprecated_2759_ = lean_ctor_get_uint8(v___y_2741_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2760_ = lean_ctor_get_uint8(v___y_2741_, sizeof(void*)*3 + 4);
v_maxRecDepth_2766_ = lean_ctor_get(v_toCold_2754_, 3);
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = lean_nat_dec_eq(v_maxRecDepth_2766_, v___x_2767_);
if (v___x_2768_ == 0)
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_nat_dec_eq(v_currRecDepth_2755_, v_maxRecDepth_2766_);
if (v___x_2769_ == 0)
{
goto v___jp_2761_;
}
else
{
lean_object* v___x_2770_; 
lean_dec_ref(v_x_2737_);
lean_inc(v_ref_2756_);
v___x_2770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2756_);
v___y_2745_ = v___x_2770_;
goto v___jp_2744_;
}
}
else
{
goto v___jp_2761_;
}
v___jp_2744_:
{
if (lean_obj_tag(v___y_2745_) == 0)
{
return v___y_2745_;
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
v_a_2746_ = lean_ctor_get(v___y_2745_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___y_2745_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___y_2745_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___y_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
v___jp_2761_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_add(v_currRecDepth_2755_, v___x_2762_);
lean_inc(v_ref_2756_);
lean_inc_ref(v_toCold_2754_);
v___x_2764_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2764_, 0, v_toCold_2754_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
lean_ctor_set(v___x_2764_, 2, v_ref_2756_);
lean_ctor_set_uint16(v___x_2764_, sizeof(void*)*3, v_optionFlags_2757_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*3 + 2, v_suppressElabErrors_2758_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*3 + 3, v_checkDeprecated_2759_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*3 + 4, v_isRecordingDeps_2760_);
lean_inc(v___y_2742_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2739_);
lean_inc(v___y_2738_);
v___x_2765_ = lean_apply_6(v_x_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___x_2764_, v___y_2742_, lean_box(0));
v___y_2745_ = v___x_2765_;
goto v___jp_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2779_, lean_object* v_pre_2780_, lean_object* v_post_2781_, lean_object* v_usedLetOnly_2782_, lean_object* v_skipConstInApp_2783_, lean_object* v_skipInstances_2784_, lean_object* v_body_2785_, lean_object* v_x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
uint8_t v_usedLetOnly_boxed_2793_; uint8_t v_skipConstInApp_boxed_2794_; uint8_t v_skipInstances_boxed_2795_; lean_object* v_res_2796_; 
v_usedLetOnly_boxed_2793_ = lean_unbox(v_usedLetOnly_2782_);
v_skipConstInApp_boxed_2794_ = lean_unbox(v_skipConstInApp_2783_);
v_skipInstances_boxed_2795_ = lean_unbox(v_skipInstances_2784_);
v_res_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2779_, v_pre_2780_, v_post_2781_, v_usedLetOnly_boxed_2793_, v_skipConstInApp_boxed_2794_, v_skipInstances_boxed_2795_, v_body_2785_, v_x_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(lean_object* v_fvars_2800_, lean_object* v_pre_2801_, lean_object* v_post_2802_, uint8_t v_usedLetOnly_2803_, uint8_t v_skipConstInApp_2804_, uint8_t v_skipInstances_2805_, lean_object* v_body_2806_, lean_object* v_x_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_array_push(v_fvars_2800_, v_x_2807_);
v___x_2815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_2801_, v_post_2802_, v_usedLetOnly_2803_, v_skipConstInApp_2804_, v_skipInstances_2805_, v___x_2814_, v_body_2806_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(lean_object* v_fvars_2816_, lean_object* v_pre_2817_, lean_object* v_post_2818_, lean_object* v_usedLetOnly_2819_, lean_object* v_skipConstInApp_2820_, lean_object* v_skipInstances_2821_, lean_object* v_body_2822_, lean_object* v_x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_usedLetOnly_boxed_2830_; uint8_t v_skipConstInApp_boxed_2831_; uint8_t v_skipInstances_boxed_2832_; lean_object* v_res_2833_; 
v_usedLetOnly_boxed_2830_ = lean_unbox(v_usedLetOnly_2819_);
v_skipConstInApp_boxed_2831_ = lean_unbox(v_skipConstInApp_2820_);
v_skipInstances_boxed_2832_ = lean_unbox(v_skipInstances_2821_);
v_res_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_2816_, v_pre_2817_, v_post_2818_, v_usedLetOnly_boxed_2830_, v_skipConstInApp_boxed_2831_, v_skipInstances_boxed_2832_, v_body_2822_, v_x_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(lean_object* v_pre_2834_, lean_object* v_post_2835_, uint8_t v_usedLetOnly_2836_, uint8_t v_skipConstInApp_2837_, uint8_t v_skipInstances_2838_, lean_object* v_e_2839_, lean_object* v_a_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
lean_inc_ref(v_post_2835_);
lean_inc(v___y_2844_);
lean_inc_ref(v___y_2843_);
lean_inc(v___y_2842_);
lean_inc_ref(v___y_2841_);
lean_inc_ref(v_e_2839_);
v___x_2846_ = lean_apply_6(v_post_2835_, v_e_2839_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, lean_box(0));
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2865_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2865_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
switch(lean_obj_tag(v_a_2847_))
{
case 0:
{
lean_object* v_e_2851_; lean_object* v___x_2853_; 
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_post_2835_);
lean_dec_ref(v_pre_2834_);
v_e_2851_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_ref(v_e_2851_);
lean_dec_ref_known(v_a_2847_, 1);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v_e_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_e_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
case 1:
{
lean_object* v_e_2855_; lean_object* v___x_2856_; 
lean_del_object(v___x_2849_);
lean_dec_ref(v_e_2839_);
v_e_2855_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_ref(v_e_2855_);
lean_dec_ref_known(v_a_2847_, 1);
v___x_2856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2834_, v_post_2835_, v_usedLetOnly_2836_, v_skipConstInApp_2837_, v_skipInstances_2838_, v_e_2855_, v_a_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2856_;
}
default: 
{
lean_object* v_e_x3f_2857_; 
lean_dec_ref(v_post_2835_);
lean_dec_ref(v_pre_2834_);
v_e_x3f_2857_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_e_x3f_2857_);
lean_dec_ref_known(v_a_2847_, 1);
if (lean_obj_tag(v_e_x3f_2857_) == 0)
{
lean_object* v___x_2859_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v_e_2839_);
v___x_2859_ = v___x_2849_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_e_2839_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2863_; 
lean_dec_ref(v_e_2839_);
v_val_2861_ = lean_ctor_get(v_e_x3f_2857_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v_e_x3f_2857_, 1);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v_val_2861_);
v___x_2863_ = v___x_2849_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_val_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_post_2835_);
lean_dec_ref(v_pre_2834_);
v_a_2866_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2846_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2846_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(lean_object* v_pre_2874_, lean_object* v_post_2875_, uint8_t v_usedLetOnly_2876_, uint8_t v_skipConstInApp_2877_, uint8_t v_skipInstances_2878_, lean_object* v_fvars_2879_, lean_object* v_e_2880_, lean_object* v_a_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
if (lean_obj_tag(v_e_2880_) == 6)
{
lean_object* v_binderName_2887_; lean_object* v_binderType_2888_; lean_object* v_body_2889_; uint8_t v_binderInfo_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_binderName_2887_ = lean_ctor_get(v_e_2880_, 0);
lean_inc(v_binderName_2887_);
v_binderType_2888_ = lean_ctor_get(v_e_2880_, 1);
lean_inc_ref(v_binderType_2888_);
v_body_2889_ = lean_ctor_get(v_e_2880_, 2);
lean_inc_ref(v_body_2889_);
v_binderInfo_2890_ = lean_ctor_get_uint8(v_e_2880_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2880_, 3);
v___x_2891_ = lean_box(v_usedLetOnly_2876_);
v___x_2892_ = lean_box(v_skipConstInApp_2877_);
v___x_2893_ = lean_box(v_skipInstances_2878_);
lean_inc_ref(v_post_2875_);
lean_inc_ref(v_pre_2874_);
lean_inc_ref(v_fvars_2879_);
v___f_2894_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2894_, 0, v_fvars_2879_);
lean_closure_set(v___f_2894_, 1, v_pre_2874_);
lean_closure_set(v___f_2894_, 2, v_post_2875_);
lean_closure_set(v___f_2894_, 3, v___x_2891_);
lean_closure_set(v___f_2894_, 4, v___x_2892_);
lean_closure_set(v___f_2894_, 5, v___x_2893_);
lean_closure_set(v___f_2894_, 6, v_body_2889_);
v___x_2895_ = lean_expr_instantiate_rev(v_binderType_2888_, v_fvars_2879_);
lean_dec_ref(v_fvars_2879_);
lean_dec_ref(v_binderType_2888_);
v___x_2896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2874_, v_post_2875_, v_usedLetOnly_2876_, v_skipConstInApp_2877_, v_skipInstances_2878_, v___x_2895_, v_a_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = 0;
v___x_2899_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2887_, v_binderInfo_2890_, v_a_2897_, v___f_2894_, v___x_2898_, v_a_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v___x_2899_;
}
else
{
lean_dec_ref(v___f_2894_);
lean_dec(v_binderName_2887_);
return v___x_2896_;
}
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_expr_instantiate_rev(v_e_2880_, v_fvars_2879_);
lean_dec_ref(v_e_2880_);
lean_inc_ref(v_post_2875_);
lean_inc_ref(v_pre_2874_);
v___x_2901_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2874_, v_post_2875_, v_usedLetOnly_2876_, v_skipConstInApp_2877_, v_skipInstances_2878_, v___x_2900_, v_a_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; uint8_t v___x_2903_; uint8_t v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = 0;
v___x_2904_ = 1;
v___x_2905_ = 1;
v___x_2906_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2879_, v_a_2902_, v___x_2903_, v_usedLetOnly_2876_, v___x_2903_, v___x_2904_, v___x_2905_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec_ref(v_fvars_2879_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v___x_2908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2874_, v_post_2875_, v_usedLetOnly_2876_, v_skipConstInApp_2877_, v_skipInstances_2878_, v_a_2907_, v_a_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v___x_2908_;
}
else
{
lean_dec_ref(v_post_2875_);
lean_dec_ref(v_pre_2874_);
return v___x_2906_;
}
}
else
{
lean_dec_ref(v_fvars_2879_);
lean_dec_ref(v_post_2875_);
lean_dec_ref(v_pre_2874_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(lean_object* v_fvars_2909_, lean_object* v_pre_2910_, lean_object* v_post_2911_, uint8_t v_usedLetOnly_2912_, uint8_t v_skipConstInApp_2913_, uint8_t v_skipInstances_2914_, lean_object* v_body_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_array_push(v_fvars_2909_, v_x_2916_);
v___x_2924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2914_, v___x_2923_, v_body_2915_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(lean_object* v_fvars_2925_, lean_object* v_pre_2926_, lean_object* v_post_2927_, lean_object* v_usedLetOnly_2928_, lean_object* v_skipConstInApp_2929_, lean_object* v_skipInstances_2930_, lean_object* v_body_2931_, lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
uint8_t v_usedLetOnly_boxed_2939_; uint8_t v_skipConstInApp_boxed_2940_; uint8_t v_skipInstances_boxed_2941_; lean_object* v_res_2942_; 
v_usedLetOnly_boxed_2939_ = lean_unbox(v_usedLetOnly_2928_);
v_skipConstInApp_boxed_2940_ = lean_unbox(v_skipConstInApp_2929_);
v_skipInstances_boxed_2941_ = lean_unbox(v_skipInstances_2930_);
v_res_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_2925_, v_pre_2926_, v_post_2927_, v_usedLetOnly_boxed_2939_, v_skipConstInApp_boxed_2940_, v_skipInstances_boxed_2941_, v_body_2931_, v_x_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(lean_object* v_pre_2943_, lean_object* v_post_2944_, uint8_t v_usedLetOnly_2945_, uint8_t v_skipConstInApp_2946_, uint8_t v_skipInstances_2947_, lean_object* v_fvars_2948_, lean_object* v_e_2949_, lean_object* v_a_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
if (lean_obj_tag(v_e_2949_) == 8)
{
lean_object* v_declName_2956_; lean_object* v_type_2957_; lean_object* v_value_2958_; lean_object* v_body_2959_; uint8_t v_nondep_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___f_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_declName_2956_ = lean_ctor_get(v_e_2949_, 0);
lean_inc(v_declName_2956_);
v_type_2957_ = lean_ctor_get(v_e_2949_, 1);
lean_inc_ref(v_type_2957_);
v_value_2958_ = lean_ctor_get(v_e_2949_, 2);
lean_inc_ref(v_value_2958_);
v_body_2959_ = lean_ctor_get(v_e_2949_, 3);
lean_inc_ref(v_body_2959_);
v_nondep_2960_ = lean_ctor_get_uint8(v_e_2949_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2949_, 4);
v___x_2961_ = lean_box(v_usedLetOnly_2945_);
v___x_2962_ = lean_box(v_skipConstInApp_2946_);
v___x_2963_ = lean_box(v_skipInstances_2947_);
lean_inc_ref_n(v_post_2944_, 2);
lean_inc_ref_n(v_pre_2943_, 2);
lean_inc_ref(v_fvars_2948_);
v___f_2964_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2964_, 0, v_fvars_2948_);
lean_closure_set(v___f_2964_, 1, v_pre_2943_);
lean_closure_set(v___f_2964_, 2, v_post_2944_);
lean_closure_set(v___f_2964_, 3, v___x_2961_);
lean_closure_set(v___f_2964_, 4, v___x_2962_);
lean_closure_set(v___f_2964_, 5, v___x_2963_);
lean_closure_set(v___f_2964_, 6, v_body_2959_);
v___x_2965_ = lean_expr_instantiate_rev(v_type_2957_, v_fvars_2948_);
lean_dec_ref(v_type_2957_);
v___x_2966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2943_, v_post_2944_, v_usedLetOnly_2945_, v_skipConstInApp_2946_, v_skipInstances_2947_, v___x_2965_, v_a_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = lean_expr_instantiate_rev(v_value_2958_, v_fvars_2948_);
lean_dec_ref(v_fvars_2948_);
lean_dec_ref(v_value_2958_);
v___x_2969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2943_, v_post_2944_, v_usedLetOnly_2945_, v_skipConstInApp_2946_, v_skipInstances_2947_, v___x_2968_, v_a_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = 0;
v___x_2972_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2956_, v_a_2967_, v_a_2970_, v___f_2964_, v_nondep_2960_, v___x_2971_, v_a_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2972_;
}
else
{
lean_dec(v_a_2967_);
lean_dec_ref(v___f_2964_);
lean_dec(v_declName_2956_);
return v___x_2969_;
}
}
else
{
lean_dec_ref(v___f_2964_);
lean_dec_ref(v_value_2958_);
lean_dec(v_declName_2956_);
lean_dec_ref(v_fvars_2948_);
lean_dec_ref(v_post_2944_);
lean_dec_ref(v_pre_2943_);
return v___x_2966_;
}
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_expr_instantiate_rev(v_e_2949_, v_fvars_2948_);
lean_dec_ref(v_e_2949_);
lean_inc_ref(v_post_2944_);
lean_inc_ref(v_pre_2943_);
v___x_2974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2943_, v_post_2944_, v_usedLetOnly_2945_, v_skipConstInApp_2946_, v_skipInstances_2947_, v___x_2973_, v_a_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; uint8_t v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = 0;
v___x_2977_ = 1;
v___x_2978_ = l_Lean_Meta_mkLetFVars(v_fvars_2948_, v_a_2975_, v_usedLetOnly_2945_, v___x_2976_, v___x_2977_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec_ref(v_fvars_2948_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_2943_, v_post_2944_, v_usedLetOnly_2945_, v_skipConstInApp_2946_, v_skipInstances_2947_, v_a_2979_, v_a_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2980_;
}
else
{
lean_dec_ref(v_post_2944_);
lean_dec_ref(v_pre_2943_);
return v___x_2978_;
}
}
else
{
lean_dec_ref(v_fvars_2948_);
lean_dec_ref(v_post_2944_);
lean_dec_ref(v_pre_2943_);
return v___x_2974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(lean_object* v_pre_2981_, lean_object* v_post_2982_, uint8_t v_usedLetOnly_2983_, uint8_t v_skipConstInApp_2984_, uint8_t v_skipInstances_2985_, size_t v_sz_2986_, size_t v_i_2987_, lean_object* v_bs_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_usize_dec_lt(v_i_2987_, v_sz_2986_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_pre_2981_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_bs_2988_);
return v___x_2996_;
}
else
{
lean_object* v_v_2997_; lean_object* v___x_2998_; lean_object* v_bs_x27_2999_; lean_object* v___x_3000_; 
v_v_2997_ = lean_array_uget(v_bs_2988_, v_i_2987_);
v___x_2998_ = lean_unsigned_to_nat(0u);
v_bs_x27_2999_ = lean_array_uset(v_bs_2988_, v_i_2987_, v___x_2998_);
lean_inc_ref(v_post_2982_);
lean_inc_ref(v_pre_2981_);
v___x_3000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2981_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v_v_2997_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_add(v_i_2987_, v___x_3002_);
v___x_3004_ = lean_array_uset(v_bs_x27_2999_, v_i_2987_, v_a_3001_);
v_i_2987_ = v___x_3003_;
v_bs_2988_ = v___x_3004_;
goto _start;
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v_bs_x27_2999_);
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_pre_2981_);
v_a_3006_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3000_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3000_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(lean_object* v_pre_3014_, lean_object* v_post_3015_, uint8_t v_usedLetOnly_3016_, uint8_t v_skipConstInApp_3017_, uint8_t v_skipInstances_3018_, lean_object* v___x_3019_, lean_object* v___y_3020_, lean_object* v_b_3021_, lean_object* v_a_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3014_, v_post_3015_, v_usedLetOnly_3016_, v_skipConstInApp_3017_, v_skipInstances_3018_, v___x_3019_, v___y_3020_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v_pre_3047_, lean_object* v_post_3048_, lean_object* v_usedLetOnly_3049_, lean_object* v_skipConstInApp_3050_, lean_object* v_skipInstances_3051_, lean_object* v___x_3052_, lean_object* v___y_3053_, lean_object* v_b_3054_, lean_object* v_a_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
uint8_t v_usedLetOnly_boxed_3061_; uint8_t v_skipConstInApp_boxed_3062_; uint8_t v_skipInstances_boxed_3063_; lean_object* v_res_3064_; 
v_usedLetOnly_boxed_3061_ = lean_unbox(v_usedLetOnly_3049_);
v_skipConstInApp_boxed_3062_ = lean_unbox(v_skipConstInApp_3050_);
v_skipInstances_boxed_3063_ = lean_unbox(v_skipInstances_3051_);
v_res_3064_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_3047_, v_post_3048_, v_usedLetOnly_boxed_3061_, v_skipConstInApp_boxed_3062_, v_skipInstances_boxed_3063_, v___x_3052_, v___y_3053_, v_b_3054_, v_a_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v_a_3055_);
lean_dec(v___y_3053_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(lean_object* v_upperBound_3065_, lean_object* v___x_3066_, lean_object* v_pre_3067_, lean_object* v_post_3068_, uint8_t v_usedLetOnly_3069_, uint8_t v_skipConstInApp_3070_, uint8_t v_skipInstances_3071_, lean_object* v_a_3072_, lean_object* v_b_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___y_3081_; uint8_t v___x_3104_; 
v___x_3104_ = lean_nat_dec_lt(v_a_3072_, v_upperBound_3065_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_post_3068_);
lean_dec_ref(v_pre_3067_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_b_3073_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_array_fget_borrowed(v_b_3073_, v_a_3072_);
v___x_3107_ = lean_array_get_size(v___x_3066_);
v___x_3108_ = lean_nat_dec_lt(v_a_3072_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___f_3112_; 
lean_inc(v___x_3106_);
v___x_3109_ = lean_box(v_usedLetOnly_3069_);
v___x_3110_ = lean_box(v_skipConstInApp_3070_);
v___x_3111_ = lean_box(v_skipInstances_3071_);
lean_inc(v_a_3072_);
lean_inc(v___y_3074_);
lean_inc_ref(v_post_3068_);
lean_inc_ref(v_pre_3067_);
v___f_3112_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3112_, 0, v_pre_3067_);
lean_closure_set(v___f_3112_, 1, v_post_3068_);
lean_closure_set(v___f_3112_, 2, v___x_3109_);
lean_closure_set(v___f_3112_, 3, v___x_3110_);
lean_closure_set(v___f_3112_, 4, v___x_3111_);
lean_closure_set(v___f_3112_, 5, v___x_3106_);
lean_closure_set(v___f_3112_, 6, v___y_3074_);
lean_closure_set(v___f_3112_, 7, v_b_3073_);
lean_closure_set(v___f_3112_, 8, v_a_3072_);
v___y_3081_ = v___f_3112_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3113_; uint8_t v_isInstance_3114_; 
v___x_3113_ = lean_array_fget_borrowed(v___x_3066_, v_a_3072_);
v_isInstance_3114_ = lean_ctor_get_uint8(v___x_3113_, sizeof(void*)*1 + 4);
if (v_isInstance_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; 
lean_inc(v___x_3106_);
v___x_3115_ = lean_box(v_usedLetOnly_3069_);
v___x_3116_ = lean_box(v_skipConstInApp_3070_);
v___x_3117_ = lean_box(v_skipInstances_3071_);
lean_inc(v_a_3072_);
lean_inc(v___y_3074_);
lean_inc_ref(v_post_3068_);
lean_inc_ref(v_pre_3067_);
v___f_3118_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3118_, 0, v_pre_3067_);
lean_closure_set(v___f_3118_, 1, v_post_3068_);
lean_closure_set(v___f_3118_, 2, v___x_3115_);
lean_closure_set(v___f_3118_, 3, v___x_3116_);
lean_closure_set(v___f_3118_, 4, v___x_3117_);
lean_closure_set(v___f_3118_, 5, v___x_3106_);
lean_closure_set(v___f_3118_, 6, v___y_3074_);
lean_closure_set(v___f_3118_, 7, v_b_3073_);
lean_closure_set(v___f_3118_, 8, v_a_3072_);
v___y_3081_ = v___f_3118_;
goto v___jp_3080_;
}
else
{
lean_object* v___x_3119_; lean_object* v___f_3120_; 
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_b_3073_);
v___f_3120_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3120_, 0, v___x_3119_);
v___y_3081_ = v___f_3120_;
goto v___jp_3080_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3082_; 
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
v___x_3082_ = lean_apply_5(v___y_3081_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, lean_box(0));
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3095_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3095_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3095_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
if (lean_obj_tag(v_a_3083_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_post_3068_);
lean_dec_ref(v_pre_3067_);
v_a_3087_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v_a_3083_, 1);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_a_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_del_object(v___x_3085_);
v_a_3091_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v_a_3083_, 1);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = lean_nat_add(v_a_3072_, v___x_3092_);
lean_dec(v_a_3072_);
v_a_3072_ = v___x_3093_;
v_b_3073_ = v_a_3091_;
goto _start;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_post_3068_);
lean_dec_ref(v_pre_3067_);
v_a_3096_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3082_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3082_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(uint8_t v_skipInstances_3121_, lean_object* v_pre_3122_, lean_object* v_post_3123_, uint8_t v_usedLetOnly_3124_, uint8_t v_skipConstInApp_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_f_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; 
if (lean_obj_tag(v_x_3126_) == 5)
{
lean_object* v_fn_3184_; lean_object* v_arg_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_fn_3184_ = lean_ctor_get(v_x_3126_, 0);
lean_inc_ref(v_fn_3184_);
v_arg_3185_ = lean_ctor_get(v_x_3126_, 1);
lean_inc_ref(v_arg_3185_);
lean_dec_ref_known(v_x_3126_, 2);
v___x_3186_ = lean_array_set(v_x_3127_, v_x_3128_, v_arg_3185_);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = lean_nat_sub(v_x_3128_, v___x_3187_);
lean_dec(v_x_3128_);
v_x_3126_ = v_fn_3184_;
v_x_3127_ = v___x_3186_;
v_x_3128_ = v___x_3188_;
goto _start;
}
else
{
lean_dec(v_x_3128_);
if (v_skipConstInApp_3125_ == 0)
{
goto v___jp_3181_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = l_Lean_Expr_isConst(v_x_3126_);
if (v___x_3190_ == 0)
{
goto v___jp_3181_;
}
else
{
v_f_3136_ = v_x_3126_;
v___y_3137_ = v___y_3129_;
v___y_3138_ = v___y_3130_;
v___y_3139_ = v___y_3131_;
v___y_3140_ = v___y_3132_;
v___y_3141_ = v___y_3133_;
goto v___jp_3135_;
}
}
}
v___jp_3135_:
{
if (v_skipInstances_3121_ == 0)
{
size_t v_sz_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v_sz_3142_ = lean_array_size(v_x_3127_);
v___x_3143_ = ((size_t)0ULL);
lean_inc_ref(v_post_3123_);
lean_inc_ref(v_pre_3122_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3121_, v_sz_3142_, v___x_3143_, v_x_3127_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = l_Lean_mkAppN(v_f_3136_, v_a_3145_);
lean_dec(v_a_3145_);
v___x_3147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3121_, v___x_3146_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3147_;
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v_f_3136_);
lean_dec_ref(v_post_3123_);
lean_dec_ref(v_pre_3122_);
v_a_3148_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3144_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3144_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_array_get_size(v_x_3127_);
lean_inc_ref(v_f_3136_);
v___x_3157_ = l_Lean_Meta_getFunInfoNArgs(v_f_3136_, v___x_3156_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v_paramInfo_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v_paramInfo_3159_ = lean_ctor_get(v_a_3158_, 0);
lean_inc_ref(v_paramInfo_3159_);
lean_dec(v_a_3158_);
v___x_3160_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3123_);
lean_inc_ref(v_pre_3122_);
v___x_3161_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_3156_, v_paramInfo_3159_, v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3121_, v___x_3160_, v_x_3127_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec_ref(v_paramInfo_3159_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = l_Lean_mkAppN(v_f_3136_, v_a_3162_);
lean_dec(v_a_3162_);
v___x_3164_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3121_, v___x_3163_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v___x_3164_;
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v_f_3136_);
lean_dec_ref(v_post_3123_);
lean_dec_ref(v_pre_3122_);
v_a_3165_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3161_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3161_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec_ref(v_f_3136_);
lean_dec_ref(v_x_3127_);
lean_dec_ref(v_post_3123_);
lean_dec_ref(v_pre_3122_);
v_a_3173_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3157_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3157_);
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
}
v___jp_3181_:
{
lean_object* v___x_3182_; 
lean_inc_ref(v_post_3123_);
lean_inc_ref(v_pre_3122_);
v___x_3182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3122_, v_post_3123_, v_usedLetOnly_3124_, v_skipConstInApp_3125_, v_skipInstances_3121_, v_x_3126_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 1);
v_f_3136_ = v_a_3183_;
v___y_3137_ = v___y_3129_;
v___y_3138_ = v___y_3130_;
v___y_3139_ = v___y_3131_;
v___y_3140_ = v___y_3132_;
v___y_3141_ = v___y_3133_;
goto v___jp_3135_;
}
else
{
lean_dec_ref(v_x_3127_);
lean_dec_ref(v_post_3123_);
lean_dec_ref(v_pre_3122_);
return v___x_3182_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(lean_object* v___x_3191_, lean_object* v_pre_3192_, lean_object* v_e_3193_, lean_object* v_post_3194_, uint8_t v_usedLetOnly_3195_, uint8_t v_skipConstInApp_3196_, uint8_t v_skipInstances_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_Core_checkSystem(v___x_3191_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3204_, 1);
lean_inc_ref(v_pre_3192_);
lean_inc(v___y_3202_);
lean_inc_ref(v___y_3201_);
lean_inc(v___y_3200_);
lean_inc_ref(v___y_3199_);
lean_inc_ref(v_e_3193_);
v___x_3205_ = lean_apply_6(v_pre_3192_, v_e_3193_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, lean_box(0));
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3254_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3254_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3254_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___y_3211_; 
switch(lean_obj_tag(v_a_3206_))
{
case 0:
{
lean_object* v_e_3246_; lean_object* v___x_3248_; 
lean_dec_ref(v_post_3194_);
lean_dec_ref(v_e_3193_);
lean_dec_ref(v_pre_3192_);
v_e_3246_ = lean_ctor_get(v_a_3206_, 0);
lean_inc_ref(v_e_3246_);
lean_dec_ref_known(v_a_3206_, 1);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v_e_3246_);
v___x_3248_ = v___x_3208_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_e_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
case 1:
{
lean_object* v_e_3250_; lean_object* v___x_3251_; 
lean_del_object(v___x_3208_);
lean_dec_ref(v_e_3193_);
v_e_3250_ = lean_ctor_get(v_a_3206_, 0);
lean_inc_ref(v_e_3250_);
lean_dec_ref_known(v_a_3206_, 1);
v___x_3251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v_e_3250_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3251_;
}
default: 
{
lean_object* v_e_x3f_3252_; 
lean_del_object(v___x_3208_);
v_e_x3f_3252_ = lean_ctor_get(v_a_3206_, 0);
lean_inc(v_e_x3f_3252_);
lean_dec_ref_known(v_a_3206_, 1);
if (lean_obj_tag(v_e_x3f_3252_) == 0)
{
v___y_3211_ = v_e_3193_;
goto v___jp_3210_;
}
else
{
lean_object* v_val_3253_; 
lean_dec_ref(v_e_3193_);
v_val_3253_ = lean_ctor_get(v_e_x3f_3252_, 0);
lean_inc(v_val_3253_);
lean_dec_ref_known(v_e_x3f_3252_, 1);
v___y_3211_ = v_val_3253_;
goto v___jp_3210_;
}
}
}
v___jp_3210_:
{
switch(lean_obj_tag(v___y_3211_))
{
case 7:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___x_3212_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3213_;
}
case 6:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3215_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___x_3214_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3215_;
}
case 8:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0));
v___x_3217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___x_3216_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3217_;
}
case 5:
{
lean_object* v_dummy_3218_; lean_object* v_nargs_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_dummy_3218_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_3219_ = l_Lean_Expr_getAppNumArgs(v___y_3211_);
lean_inc(v_nargs_3219_);
v___x_3220_ = lean_mk_array(v_nargs_3219_, v_dummy_3218_);
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_sub(v_nargs_3219_, v___x_3221_);
lean_dec(v_nargs_3219_);
v___x_3223_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_3197_, v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v___y_3211_, v___x_3220_, v___x_3222_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3223_;
}
case 10:
{
lean_object* v_data_3224_; lean_object* v_expr_3225_; lean_object* v___x_3226_; 
v_data_3224_ = lean_ctor_get(v___y_3211_, 0);
v_expr_3225_ = lean_ctor_get(v___y_3211_, 1);
lean_inc_ref(v_expr_3225_);
lean_inc_ref(v_post_3194_);
lean_inc_ref(v_pre_3192_);
v___x_3226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v_expr_3225_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; size_t v___x_3228_; size_t v___x_3229_; uint8_t v___x_3230_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = lean_ptr_addr(v_expr_3225_);
v___x_3229_ = lean_ptr_addr(v_a_3227_);
v___x_3230_ = lean_usize_dec_eq(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_inc(v_data_3224_);
lean_dec_ref_known(v___y_3211_, 2);
v___x_3231_ = l_Lean_Expr_mdata___override(v_data_3224_, v_a_3227_);
v___x_3232_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___x_3231_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; 
lean_dec(v_a_3227_);
v___x_3233_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3233_;
}
}
else
{
lean_dec_ref_known(v___y_3211_, 2);
lean_dec_ref(v_post_3194_);
lean_dec_ref(v_pre_3192_);
return v___x_3226_;
}
}
case 11:
{
lean_object* v_typeName_3234_; lean_object* v_idx_3235_; lean_object* v_struct_3236_; lean_object* v___x_3237_; 
v_typeName_3234_ = lean_ctor_get(v___y_3211_, 0);
v_idx_3235_ = lean_ctor_get(v___y_3211_, 1);
v_struct_3236_ = lean_ctor_get(v___y_3211_, 2);
lean_inc_ref(v_struct_3236_);
lean_inc_ref(v_post_3194_);
lean_inc_ref(v_pre_3192_);
v___x_3237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v_struct_3236_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; size_t v___x_3239_; size_t v___x_3240_; uint8_t v___x_3241_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = lean_ptr_addr(v_struct_3236_);
v___x_3240_ = lean_ptr_addr(v_a_3238_);
v___x_3241_ = lean_usize_dec_eq(v___x_3239_, v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_inc(v_idx_3235_);
lean_inc(v_typeName_3234_);
lean_dec_ref_known(v___y_3211_, 3);
v___x_3242_ = l_Lean_Expr_proj___override(v_typeName_3234_, v_idx_3235_, v_a_3238_);
v___x_3243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___x_3242_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; 
lean_dec(v_a_3238_);
v___x_3244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3244_;
}
}
else
{
lean_dec_ref_known(v___y_3211_, 3);
lean_dec_ref(v_post_3194_);
lean_dec_ref(v_pre_3192_);
return v___x_3237_;
}
}
default: 
{
lean_object* v___x_3245_; 
v___x_3245_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3192_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v_skipInstances_3197_, v___y_3211_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3245_;
}
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_post_3194_);
lean_dec_ref(v_e_3193_);
lean_dec_ref(v_pre_3192_);
v_a_3255_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3205_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3205_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_post_3194_);
lean_dec_ref(v_e_3193_);
lean_dec_ref(v_pre_3192_);
v_a_3263_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3204_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3204_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(lean_object* v___x_3271_, lean_object* v_pre_3272_, lean_object* v_e_3273_, lean_object* v_post_3274_, lean_object* v_usedLetOnly_3275_, lean_object* v_skipConstInApp_3276_, lean_object* v_skipInstances_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v_usedLetOnly_boxed_3284_; uint8_t v_skipConstInApp_boxed_3285_; uint8_t v_skipInstances_boxed_3286_; lean_object* v_res_3287_; 
v_usedLetOnly_boxed_3284_ = lean_unbox(v_usedLetOnly_3275_);
v_skipConstInApp_boxed_3285_ = lean_unbox(v_skipConstInApp_3276_);
v_skipInstances_boxed_3286_ = lean_unbox(v_skipInstances_3277_);
v_res_3287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_3271_, v_pre_3272_, v_e_3273_, v_post_3274_, v_usedLetOnly_boxed_3284_, v_skipConstInApp_boxed_3285_, v_skipInstances_boxed_3286_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(lean_object* v_pre_3288_, lean_object* v_post_3289_, uint8_t v_usedLetOnly_3290_, uint8_t v_skipConstInApp_3291_, uint8_t v_skipInstances_3292_, lean_object* v_e_3293_, lean_object* v_a_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
lean_inc(v_a_3294_);
v___x_3300_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3300_, 0, lean_box(0));
lean_closure_set(v___x_3300_, 1, lean_box(0));
lean_closure_set(v___x_3300_, 2, v_a_3294_);
v___x_3301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___x_3300_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3336_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3336_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3336_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_3302_, v_e_3293_);
lean_dec(v_a_3302_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; 
lean_del_object(v___x_3304_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0));
v___x_3308_ = lean_box(v_usedLetOnly_3290_);
v___x_3309_ = lean_box(v_skipConstInApp_3291_);
v___x_3310_ = lean_box(v_skipInstances_3292_);
lean_inc_ref(v_e_3293_);
v___f_3311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3311_, 0, v___x_3307_);
lean_closure_set(v___f_3311_, 1, v_pre_3288_);
lean_closure_set(v___f_3311_, 2, v_e_3293_);
lean_closure_set(v___f_3311_, 3, v_post_3289_);
lean_closure_set(v___f_3311_, 4, v___x_3308_);
lean_closure_set(v___f_3311_, 5, v___x_3309_);
lean_closure_set(v___f_3311_, 6, v___x_3310_);
v___x_3312_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_3311_, v_a_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___f_3314_; lean_object* v___x_3315_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_n(v_a_3313_, 2);
lean_dec_ref_known(v___x_3312_, 1);
lean_inc(v_a_3294_);
v___f_3314_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3314_, 0, v_a_3294_);
lean_closure_set(v___f_3314_, 1, v_e_3293_);
lean_closure_set(v___f_3314_, 2, v_a_3313_);
v___x_3315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_box(0), v___f_3314_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; 
v_unused_3323_ = lean_ctor_get(v___x_3315_, 0);
lean_dec(v_unused_3323_);
v___x_3317_ = v___x_3315_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_dec(v___x_3315_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3320_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v_a_3313_);
v___x_3320_ = v___x_3317_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3313_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_a_3313_);
v_a_3324_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3315_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3315_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_dec_ref(v_e_3293_);
return v___x_3312_;
}
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3334_; 
lean_dec_ref(v_e_3293_);
lean_dec_ref(v_post_3289_);
lean_dec_ref(v_pre_3288_);
v_val_3332_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v___x_3306_, 1);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_val_3332_);
v___x_3334_ = v___x_3304_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_val_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v_e_3293_);
lean_dec_ref(v_post_3289_);
lean_dec_ref(v_pre_3288_);
v_a_3337_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3301_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3301_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3345_, lean_object* v_post_3346_, uint8_t v_usedLetOnly_3347_, uint8_t v_skipConstInApp_3348_, uint8_t v_skipInstances_3349_, lean_object* v_fvars_3350_, lean_object* v_e_3351_, lean_object* v_a_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
if (lean_obj_tag(v_e_3351_) == 7)
{
lean_object* v_binderName_3358_; lean_object* v_binderType_3359_; lean_object* v_body_3360_; uint8_t v_binderInfo_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_binderName_3358_ = lean_ctor_get(v_e_3351_, 0);
lean_inc(v_binderName_3358_);
v_binderType_3359_ = lean_ctor_get(v_e_3351_, 1);
lean_inc_ref(v_binderType_3359_);
v_body_3360_ = lean_ctor_get(v_e_3351_, 2);
lean_inc_ref(v_body_3360_);
v_binderInfo_3361_ = lean_ctor_get_uint8(v_e_3351_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3351_, 3);
v___x_3362_ = lean_box(v_usedLetOnly_3347_);
v___x_3363_ = lean_box(v_skipConstInApp_3348_);
v___x_3364_ = lean_box(v_skipInstances_3349_);
lean_inc_ref(v_post_3346_);
lean_inc_ref(v_pre_3345_);
lean_inc_ref(v_fvars_3350_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3365_, 0, v_fvars_3350_);
lean_closure_set(v___f_3365_, 1, v_pre_3345_);
lean_closure_set(v___f_3365_, 2, v_post_3346_);
lean_closure_set(v___f_3365_, 3, v___x_3362_);
lean_closure_set(v___f_3365_, 4, v___x_3363_);
lean_closure_set(v___f_3365_, 5, v___x_3364_);
lean_closure_set(v___f_3365_, 6, v_body_3360_);
v___x_3366_ = lean_expr_instantiate_rev(v_binderType_3359_, v_fvars_3350_);
lean_dec_ref(v_fvars_3350_);
lean_dec_ref(v_binderType_3359_);
v___x_3367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3345_, v_post_3346_, v_usedLetOnly_3347_, v_skipConstInApp_3348_, v_skipInstances_3349_, v___x_3366_, v_a_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v___x_3369_ = 0;
v___x_3370_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3358_, v_binderInfo_3361_, v_a_3368_, v___f_3365_, v___x_3369_, v_a_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
return v___x_3370_;
}
else
{
lean_dec_ref(v___f_3365_);
lean_dec(v_binderName_3358_);
return v___x_3367_;
}
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_expr_instantiate_rev(v_e_3351_, v_fvars_3350_);
lean_dec_ref(v_e_3351_);
lean_inc_ref(v_post_3346_);
lean_inc_ref(v_pre_3345_);
v___x_3372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3345_, v_post_3346_, v_usedLetOnly_3347_, v_skipConstInApp_3348_, v_skipInstances_3349_, v___x_3371_, v_a_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; uint8_t v___x_3374_; uint8_t v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = 0;
v___x_3375_ = 1;
v___x_3376_ = 1;
v___x_3377_ = l_Lean_Meta_mkForallFVars(v_fvars_3350_, v_a_3373_, v___x_3374_, v_usedLetOnly_3347_, v___x_3375_, v___x_3376_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec_ref(v_fvars_3350_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3345_, v_post_3346_, v_usedLetOnly_3347_, v_skipConstInApp_3348_, v_skipInstances_3349_, v_a_3378_, v_a_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
return v___x_3379_;
}
else
{
lean_dec_ref(v_post_3346_);
lean_dec_ref(v_pre_3345_);
return v___x_3377_;
}
}
else
{
lean_dec_ref(v_fvars_3350_);
lean_dec_ref(v_post_3346_);
lean_dec_ref(v_pre_3345_);
return v___x_3372_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(lean_object* v_fvars_3380_, lean_object* v_pre_3381_, lean_object* v_post_3382_, uint8_t v_usedLetOnly_3383_, uint8_t v_skipConstInApp_3384_, uint8_t v_skipInstances_3385_, lean_object* v_body_3386_, lean_object* v_x_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_array_push(v_fvars_3380_, v_x_3387_);
v___x_3395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3381_, v_post_3382_, v_usedLetOnly_3383_, v_skipConstInApp_3384_, v_skipInstances_3385_, v___x_3394_, v_body_3386_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_3396_, lean_object* v_post_3397_, lean_object* v_usedLetOnly_3398_, lean_object* v_skipConstInApp_3399_, lean_object* v_skipInstances_3400_, lean_object* v_e_3401_, lean_object* v_a_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v_usedLetOnly_boxed_3408_; uint8_t v_skipConstInApp_boxed_3409_; uint8_t v_skipInstances_boxed_3410_; lean_object* v_res_3411_; 
v_usedLetOnly_boxed_3408_ = lean_unbox(v_usedLetOnly_3398_);
v_skipConstInApp_boxed_3409_ = lean_unbox(v_skipConstInApp_3399_);
v_skipInstances_boxed_3410_ = lean_unbox(v_skipInstances_3400_);
v_res_3411_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3396_, v_post_3397_, v_usedLetOnly_boxed_3408_, v_skipConstInApp_boxed_3409_, v_skipInstances_boxed_3410_, v_e_3401_, v_a_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_a_3402_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_3412_, lean_object* v_post_3413_, lean_object* v_usedLetOnly_3414_, lean_object* v_skipConstInApp_3415_, lean_object* v_skipInstances_3416_, lean_object* v_sz_3417_, lean_object* v_i_3418_, lean_object* v_bs_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v_usedLetOnly_boxed_3426_; uint8_t v_skipConstInApp_boxed_3427_; uint8_t v_skipInstances_boxed_3428_; size_t v_sz_boxed_3429_; size_t v_i_boxed_3430_; lean_object* v_res_3431_; 
v_usedLetOnly_boxed_3426_ = lean_unbox(v_usedLetOnly_3414_);
v_skipConstInApp_boxed_3427_ = lean_unbox(v_skipConstInApp_3415_);
v_skipInstances_boxed_3428_ = lean_unbox(v_skipInstances_3416_);
v_sz_boxed_3429_ = lean_unbox_usize(v_sz_3417_);
lean_dec(v_sz_3417_);
v_i_boxed_3430_ = lean_unbox_usize(v_i_3418_);
lean_dec(v_i_3418_);
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_3412_, v_post_3413_, v_usedLetOnly_boxed_3426_, v_skipConstInApp_boxed_3427_, v_skipInstances_boxed_3428_, v_sz_boxed_3429_, v_i_boxed_3430_, v_bs_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(lean_object* v_pre_3432_, lean_object* v_post_3433_, lean_object* v_usedLetOnly_3434_, lean_object* v_skipConstInApp_3435_, lean_object* v_skipInstances_3436_, lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v_usedLetOnly_boxed_3444_; uint8_t v_skipConstInApp_boxed_3445_; uint8_t v_skipInstances_boxed_3446_; lean_object* v_res_3447_; 
v_usedLetOnly_boxed_3444_ = lean_unbox(v_usedLetOnly_3434_);
v_skipConstInApp_boxed_3445_ = lean_unbox(v_skipConstInApp_3435_);
v_skipInstances_boxed_3446_ = lean_unbox(v_skipInstances_3436_);
v_res_3447_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3432_, v_post_3433_, v_usedLetOnly_boxed_3444_, v_skipConstInApp_boxed_3445_, v_skipInstances_boxed_3446_, v_e_3437_, v_a_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v_a_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(lean_object* v_pre_3448_, lean_object* v_post_3449_, lean_object* v_usedLetOnly_3450_, lean_object* v_skipConstInApp_3451_, lean_object* v_skipInstances_3452_, lean_object* v_fvars_3453_, lean_object* v_e_3454_, lean_object* v_a_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_usedLetOnly_boxed_3461_; uint8_t v_skipConstInApp_boxed_3462_; uint8_t v_skipInstances_boxed_3463_; lean_object* v_res_3464_; 
v_usedLetOnly_boxed_3461_ = lean_unbox(v_usedLetOnly_3450_);
v_skipConstInApp_boxed_3462_ = lean_unbox(v_skipConstInApp_3451_);
v_skipInstances_boxed_3463_ = lean_unbox(v_skipInstances_3452_);
v_res_3464_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_3448_, v_post_3449_, v_usedLetOnly_boxed_3461_, v_skipConstInApp_boxed_3462_, v_skipInstances_boxed_3463_, v_fvars_3453_, v_e_3454_, v_a_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v_a_3455_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(lean_object* v_pre_3465_, lean_object* v_post_3466_, lean_object* v_usedLetOnly_3467_, lean_object* v_skipConstInApp_3468_, lean_object* v_skipInstances_3469_, lean_object* v_fvars_3470_, lean_object* v_e_3471_, lean_object* v_a_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
uint8_t v_usedLetOnly_boxed_3478_; uint8_t v_skipConstInApp_boxed_3479_; uint8_t v_skipInstances_boxed_3480_; lean_object* v_res_3481_; 
v_usedLetOnly_boxed_3478_ = lean_unbox(v_usedLetOnly_3467_);
v_skipConstInApp_boxed_3479_ = lean_unbox(v_skipConstInApp_3468_);
v_skipInstances_boxed_3480_ = lean_unbox(v_skipInstances_3469_);
v_res_3481_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_3465_, v_post_3466_, v_usedLetOnly_boxed_3478_, v_skipConstInApp_boxed_3479_, v_skipInstances_boxed_3480_, v_fvars_3470_, v_e_3471_, v_a_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v_a_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(lean_object* v_pre_3482_, lean_object* v_post_3483_, lean_object* v_usedLetOnly_3484_, lean_object* v_skipConstInApp_3485_, lean_object* v_skipInstances_3486_, lean_object* v_fvars_3487_, lean_object* v_e_3488_, lean_object* v_a_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v_usedLetOnly_boxed_3495_; uint8_t v_skipConstInApp_boxed_3496_; uint8_t v_skipInstances_boxed_3497_; lean_object* v_res_3498_; 
v_usedLetOnly_boxed_3495_ = lean_unbox(v_usedLetOnly_3484_);
v_skipConstInApp_boxed_3496_ = lean_unbox(v_skipConstInApp_3485_);
v_skipInstances_boxed_3497_ = lean_unbox(v_skipInstances_3486_);
v_res_3498_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_3482_, v_post_3483_, v_usedLetOnly_boxed_3495_, v_skipConstInApp_boxed_3496_, v_skipInstances_boxed_3497_, v_fvars_3487_, v_e_3488_, v_a_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_a_3489_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_3499_, lean_object* v___x_3500_, lean_object* v_pre_3501_, lean_object* v_post_3502_, lean_object* v_usedLetOnly_3503_, lean_object* v_skipConstInApp_3504_, lean_object* v_skipInstances_3505_, lean_object* v_a_3506_, lean_object* v_b_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_usedLetOnly_boxed_3514_; uint8_t v_skipConstInApp_boxed_3515_; uint8_t v_skipInstances_boxed_3516_; lean_object* v_res_3517_; 
v_usedLetOnly_boxed_3514_ = lean_unbox(v_usedLetOnly_3503_);
v_skipConstInApp_boxed_3515_ = lean_unbox(v_skipConstInApp_3504_);
v_skipInstances_boxed_3516_ = lean_unbox(v_skipInstances_3505_);
v_res_3517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3499_, v___x_3500_, v_pre_3501_, v_post_3502_, v_usedLetOnly_boxed_3514_, v_skipConstInApp_boxed_3515_, v_skipInstances_boxed_3516_, v_a_3506_, v_b_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___x_3500_);
lean_dec(v_upperBound_3499_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(lean_object* v_skipInstances_3518_, lean_object* v_pre_3519_, lean_object* v_post_3520_, lean_object* v_usedLetOnly_3521_, lean_object* v_skipConstInApp_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
uint8_t v_skipInstances_boxed_3532_; uint8_t v_usedLetOnly_boxed_3533_; uint8_t v_skipConstInApp_boxed_3534_; lean_object* v_res_3535_; 
v_skipInstances_boxed_3532_ = lean_unbox(v_skipInstances_3518_);
v_usedLetOnly_boxed_3533_ = lean_unbox(v_usedLetOnly_3521_);
v_skipConstInApp_boxed_3534_ = lean_unbox(v_skipConstInApp_3522_);
v_res_3535_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_3532_, v_pre_3519_, v_post_3520_, v_usedLetOnly_boxed_3533_, v_skipConstInApp_boxed_3534_, v_x_3523_, v_x_3524_, v_x_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
return v_res_3535_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_unsigned_to_nat(16u);
v___x_3538_ = lean_mk_array(v___x_3537_, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1);
v___x_3543_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3543_, 0, lean_box(0));
lean_closure_set(v___x_3543_, 1, lean_box(0));
lean_closure_set(v___x_3543_, 2, v___x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(lean_object* v_input_3544_, lean_object* v_pre_3545_, lean_object* v_post_3546_, uint8_t v_usedLetOnly_3547_, uint8_t v_skipConstInApp_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v_a_3557_; lean_object* v___x_3558_; 
v___x_3554_ = 0;
v___x_3555_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3556_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3555_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3545_, v_post_3546_, v_usedLetOnly_3547_, v_skipConstInApp_3548_, v___x_3554_, v_input_3544_, v_a_3557_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v___x_3560_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3560_, 0, lean_box(0));
lean_closure_set(v___x_3560_, 1, lean_box(0));
lean_closure_set(v___x_3560_, 2, v_a_3557_);
v___x_3561_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3560_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v___x_3561_, 0);
lean_dec(v_unused_3569_);
v___x_3563_ = v___x_3561_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v___x_3561_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v_a_3559_);
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3559_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
else
{
lean_dec(v_a_3557_);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(lean_object* v_input_3570_, lean_object* v_pre_3571_, lean_object* v_post_3572_, lean_object* v_usedLetOnly_3573_, lean_object* v_skipConstInApp_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v_usedLetOnly_boxed_3580_; uint8_t v_skipConstInApp_boxed_3581_; lean_object* v_res_3582_; 
v_usedLetOnly_boxed_3580_ = lean_unbox(v_usedLetOnly_3573_);
v_skipConstInApp_boxed_3581_ = lean_unbox(v_skipConstInApp_3574_);
v_res_3582_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_input_3570_, v_pre_3571_, v_post_3572_, v_usedLetOnly_boxed_3580_, v_skipConstInApp_boxed_3581_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3584_, lean_object* v_p_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; 
v___f_3591_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3592_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3592_, 0, v_p_3585_);
v___x_3593_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3584_, v_a_3587_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = 0;
v___x_3596_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3594_, v___f_3591_, v___f_3592_, v___x_3595_, v___x_3595_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3597_, lean_object* v_p_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Meta_etaStructReduce(v_e_3597_, v_p_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(lean_object* v_upperBound_3605_, lean_object* v___x_3606_, lean_object* v_pre_3607_, lean_object* v_post_3608_, uint8_t v_usedLetOnly_3609_, uint8_t v_skipConstInApp_3610_, uint8_t v_skipInstances_3611_, lean_object* v___x_3612_, lean_object* v_inst_3613_, lean_object* v_R_3614_, lean_object* v_a_3615_, lean_object* v_b_3616_, lean_object* v_c_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_3605_, v___x_3606_, v_pre_3607_, v_post_3608_, v_usedLetOnly_3609_, v_skipConstInApp_3610_, v_skipInstances_3611_, v_a_3615_, v_b_3616_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3625_ = _args[0];
lean_object* v___x_3626_ = _args[1];
lean_object* v_pre_3627_ = _args[2];
lean_object* v_post_3628_ = _args[3];
lean_object* v_usedLetOnly_3629_ = _args[4];
lean_object* v_skipConstInApp_3630_ = _args[5];
lean_object* v_skipInstances_3631_ = _args[6];
lean_object* v___x_3632_ = _args[7];
lean_object* v_inst_3633_ = _args[8];
lean_object* v_R_3634_ = _args[9];
lean_object* v_a_3635_ = _args[10];
lean_object* v_b_3636_ = _args[11];
lean_object* v_c_3637_ = _args[12];
lean_object* v___y_3638_ = _args[13];
lean_object* v___y_3639_ = _args[14];
lean_object* v___y_3640_ = _args[15];
lean_object* v___y_3641_ = _args[16];
lean_object* v___y_3642_ = _args[17];
lean_object* v___y_3643_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3644_; uint8_t v_skipConstInApp_boxed_3645_; uint8_t v_skipInstances_boxed_3646_; lean_object* v_res_3647_; 
v_usedLetOnly_boxed_3644_ = lean_unbox(v_usedLetOnly_3629_);
v_skipConstInApp_boxed_3645_ = lean_unbox(v_skipConstInApp_3630_);
v_skipInstances_boxed_3646_ = lean_unbox(v_skipInstances_3631_);
v_res_3647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_3625_, v___x_3626_, v_pre_3627_, v_post_3628_, v_usedLetOnly_boxed_3644_, v_skipConstInApp_boxed_3645_, v_skipInstances_boxed_3646_, v___x_3632_, v_inst_3633_, v_R_3634_, v_a_3635_, v_b_3636_, v_c_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec(v___x_3632_);
lean_dec_ref(v___x_3626_);
lean_dec(v_upperBound_3625_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3648_, lean_object* v_m_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_3649_, v_a_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3652_, lean_object* v_m_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_3652_, v_m_3653_, v_a_3654_);
lean_dec_ref(v_a_3654_);
lean_dec_ref(v_m_3653_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_3656_, lean_object* v_name_3657_, uint8_t v_bi_3658_, lean_object* v_type_3659_, lean_object* v_k_3660_, uint8_t v_kind_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_3657_, v_bi_3658_, v_type_3659_, v_k_3660_, v_kind_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_name_3670_, lean_object* v_bi_3671_, lean_object* v_type_3672_, lean_object* v_k_3673_, lean_object* v_kind_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
uint8_t v_bi_boxed_3681_; uint8_t v_kind_boxed_3682_; lean_object* v_res_3683_; 
v_bi_boxed_3681_ = lean_unbox(v_bi_3671_);
v_kind_boxed_3682_ = lean_unbox(v_kind_3674_);
v_res_3683_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_3669_, v_name_3670_, v_bi_boxed_3681_, v_type_3672_, v_k_3673_, v_kind_boxed_3682_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(lean_object* v_00_u03b1_3684_, lean_object* v_name_3685_, lean_object* v_type_3686_, lean_object* v_val_3687_, lean_object* v_k_3688_, uint8_t v_nondep_3689_, uint8_t v_kind_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_3685_, v_type_3686_, v_val_3687_, v_k_3688_, v_nondep_3689_, v_kind_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(lean_object* v_00_u03b1_3698_, lean_object* v_name_3699_, lean_object* v_type_3700_, lean_object* v_val_3701_, lean_object* v_k_3702_, lean_object* v_nondep_3703_, lean_object* v_kind_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
uint8_t v_nondep_boxed_3711_; uint8_t v_kind_boxed_3712_; lean_object* v_res_3713_; 
v_nondep_boxed_3711_ = lean_unbox(v_nondep_3703_);
v_kind_boxed_3712_ = lean_unbox(v_kind_3704_);
v_res_3713_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_3698_, v_name_3699_, v_type_3700_, v_val_3701_, v_k_3702_, v_nondep_boxed_3711_, v_kind_boxed_3712_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(lean_object* v_00_u03b1_3714_, lean_object* v_ref_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_3715_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(lean_object* v_00_u03b1_3722_, lean_object* v_ref_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_3722_, v_ref_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(lean_object* v_00_u03b1_3730_, lean_object* v_x_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_x_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_3739_, v_x_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(lean_object* v_00_u03b2_3748_, lean_object* v_m_3749_, lean_object* v_a_3750_, lean_object* v_b_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_3749_, v_a_3750_, v_b_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b2_3753_, lean_object* v_a_3754_, lean_object* v_x_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_3754_, v_x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b2_3757_, lean_object* v_a_3758_, lean_object* v_x_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_3757_, v_a_3758_, v_x_3759_);
lean_dec(v_x_3759_);
lean_dec_ref(v_a_3758_);
return v_res_3760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(lean_object* v_00_u03b2_3761_, lean_object* v_a_3762_, lean_object* v_x_3763_){
_start:
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_3762_, v_x_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(lean_object* v_00_u03b2_3765_, lean_object* v_a_3766_, lean_object* v_x_3767_){
_start:
{
uint8_t v_res_3768_; lean_object* v_r_3769_; 
v_res_3768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_3765_, v_a_3766_, v_x_3767_);
lean_dec(v_x_3767_);
lean_dec_ref(v_a_3766_);
v_r_3769_ = lean_box(v_res_3768_);
return v_r_3769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(lean_object* v_00_u03b2_3770_, lean_object* v_data_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(lean_object* v_00_u03b2_3773_, lean_object* v_a_3774_, lean_object* v_b_3775_, lean_object* v_x_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_3774_, v_b_3775_, v_x_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3778_, lean_object* v_i_3779_, lean_object* v_source_3780_, lean_object* v_target_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_3779_, v_source_3780_, v_target_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(lean_object* v_00_u03b2_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_3784_, v_x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(lean_object* v_binderType_3787_, lean_object* v_inst_3788_, lean_object* v_toBind_3789_, lean_object* v___f_3790_, lean_object* v_____do__lift_3791_){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3792_, 0, v_____do__lift_3791_);
lean_closure_set(v___x_3792_, 1, v_binderType_3787_);
v___x_3793_ = lean_apply_2(v_inst_3788_, lean_box(0), v___x_3792_);
v___x_3794_ = lean_apply_4(v_toBind_3789_, lean_box(0), lean_box(0), v___x_3793_, v___f_3790_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(lean_object* v_toPure_3795_, lean_object* v_usedFields_3796_, lean_object* v_binderName_3797_, lean_object* v_body_3798_, lean_object* v_val_3799_, lean_object* v_inst_3800_, lean_object* v_inst_3801_, lean_object* v_fieldVal_x3f_3802_, lean_object* v_____do__lift_3803_){
_start:
{
uint8_t v_____do__lift_285__boxed_3804_; lean_object* v_res_3805_; 
v_____do__lift_285__boxed_3804_ = lean_unbox(v_____do__lift_3803_);
v_res_3805_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3795_, v_usedFields_3796_, v_binderName_3797_, v_body_3798_, v_val_3799_, v_inst_3800_, v_inst_3801_, v_fieldVal_x3f_3802_, v_____do__lift_285__boxed_3804_);
lean_dec_ref(v_val_3799_);
lean_dec_ref(v_body_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(lean_object* v_toPure_3806_, lean_object* v_usedFields_3807_, lean_object* v_binderName_3808_, lean_object* v_body_3809_, lean_object* v_inst_3810_, lean_object* v_inst_3811_, lean_object* v_fieldVal_x3f_3812_, lean_object* v_binderType_3813_, lean_object* v_toBind_3814_, lean_object* v_____x_3815_){
_start:
{
if (lean_obj_tag(v_____x_3815_) == 1)
{
lean_object* v_val_3816_; lean_object* v___f_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_val_3816_ = lean_ctor_get(v_____x_3815_, 0);
lean_inc_n(v_val_3816_, 2);
lean_dec_ref_known(v_____x_3815_, 1);
lean_inc_n(v_inst_3811_, 2);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_3817_, 0, v_toPure_3806_);
lean_closure_set(v___f_3817_, 1, v_usedFields_3807_);
lean_closure_set(v___f_3817_, 2, v_binderName_3808_);
lean_closure_set(v___f_3817_, 3, v_body_3809_);
lean_closure_set(v___f_3817_, 4, v_val_3816_);
lean_closure_set(v___f_3817_, 5, v_inst_3810_);
lean_closure_set(v___f_3817_, 6, v_inst_3811_);
lean_closure_set(v___f_3817_, 7, v_fieldVal_x3f_3812_);
lean_inc(v_toBind_3814_);
v___f_3818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1), 5, 4);
lean_closure_set(v___f_3818_, 0, v_binderType_3813_);
lean_closure_set(v___f_3818_, 1, v_inst_3811_);
lean_closure_set(v___f_3818_, 2, v_toBind_3814_);
lean_closure_set(v___f_3818_, 3, v___f_3817_);
v___x_3819_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3819_, 0, v_val_3816_);
v___x_3820_ = lean_apply_2(v_inst_3811_, lean_box(0), v___x_3819_);
v___x_3821_ = lean_apply_4(v_toBind_3814_, lean_box(0), lean_box(0), v___x_3820_, v___f_3818_);
return v___x_3821_;
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_dec(v_____x_3815_);
lean_dec(v_toBind_3814_);
lean_dec_ref(v_binderType_3813_);
lean_dec(v_fieldVal_x3f_3812_);
lean_dec(v_inst_3811_);
lean_dec_ref(v_inst_3810_);
lean_dec_ref(v_body_3809_);
lean_dec(v_binderName_3808_);
lean_dec(v_usedFields_3807_);
v___x_3822_ = lean_box(0);
v___x_3823_ = lean_apply_2(v_toPure_3806_, lean_box(0), v___x_3822_);
return v___x_3823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(lean_object* v_inst_3827_, lean_object* v_inst_3828_, lean_object* v_fieldVal_x3f_3829_, lean_object* v_usedFields_3830_, lean_object* v_e_3831_){
_start:
{
lean_object* v_toApplicative_3832_; lean_object* v_toBind_3833_; lean_object* v_toPure_3834_; 
v_toApplicative_3832_ = lean_ctor_get(v_inst_3827_, 0);
v_toBind_3833_ = lean_ctor_get(v_inst_3827_, 1);
v_toPure_3834_ = lean_ctor_get(v_toApplicative_3832_, 1);
lean_inc(v_toPure_3834_);
if (lean_obj_tag(v_e_3831_) == 6)
{
lean_object* v_binderName_3839_; lean_object* v_binderType_3840_; lean_object* v_body_3841_; lean_object* v___f_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_inc_n(v_toBind_3833_, 2);
v_binderName_3839_ = lean_ctor_get(v_e_3831_, 0);
lean_inc_n(v_binderName_3839_, 2);
v_binderType_3840_ = lean_ctor_get(v_e_3831_, 1);
lean_inc_ref(v_binderType_3840_);
v_body_3841_ = lean_ctor_get(v_e_3831_, 2);
lean_inc_ref(v_body_3841_);
lean_dec_ref_known(v_e_3831_, 3);
lean_inc(v_fieldVal_x3f_3829_);
v___f_3842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2), 10, 9);
lean_closure_set(v___f_3842_, 0, v_toPure_3834_);
lean_closure_set(v___f_3842_, 1, v_usedFields_3830_);
lean_closure_set(v___f_3842_, 2, v_binderName_3839_);
lean_closure_set(v___f_3842_, 3, v_body_3841_);
lean_closure_set(v___f_3842_, 4, v_inst_3827_);
lean_closure_set(v___f_3842_, 5, v_inst_3828_);
lean_closure_set(v___f_3842_, 6, v_fieldVal_x3f_3829_);
lean_closure_set(v___f_3842_, 7, v_binderType_3840_);
lean_closure_set(v___f_3842_, 8, v_toBind_3833_);
v___x_3843_ = lean_apply_1(v_fieldVal_x3f_3829_, v_binderName_3839_);
v___x_3844_ = lean_apply_4(v_toBind_3833_, lean_box(0), lean_box(0), v___x_3843_, v___f_3842_);
return v___x_3844_;
}
else
{
lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_fieldVal_x3f_3829_);
lean_dec(v_inst_3828_);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_inst_3827_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; lean_object* v_unused_3863_; 
v_unused_3862_ = lean_ctor_get(v_inst_3827_, 1);
lean_dec(v_unused_3862_);
v_unused_3863_ = lean_ctor_get(v_inst_3827_, 0);
lean_dec(v_unused_3863_);
v___x_3846_ = v_inst_3827_;
v_isShared_3847_ = v_isSharedCheck_3861_;
goto v_resetjp_3845_;
}
else
{
lean_dec(v_inst_3827_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3861_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3848_; uint8_t v___x_3849_; 
v___x_3848_ = l_Lean_Expr_cleanupAnnotations(v_e_3831_);
v___x_3849_ = l_Lean_Expr_isApp(v___x_3848_);
if (v___x_3849_ == 0)
{
lean_dec_ref(v___x_3848_);
lean_del_object(v___x_3846_);
goto v___jp_3835_;
}
else
{
lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3848_);
v___x_3851_ = l_Lean_Expr_isApp(v___x_3850_);
if (v___x_3851_ == 0)
{
lean_dec_ref(v___x_3850_);
lean_dec_ref(v___x_3848_);
lean_del_object(v___x_3846_);
goto v___jp_3835_;
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; 
v___x_3852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3850_);
lean_dec_ref(v___x_3850_);
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3854_ = l_Lean_Expr_isConstOf(v___x_3852_, v___x_3853_);
lean_dec_ref(v___x_3852_);
if (v___x_3854_ == 0)
{
lean_dec_ref(v___x_3848_);
lean_del_object(v___x_3846_);
goto v___jp_3835_;
}
else
{
lean_object* v_arg_3855_; lean_object* v___x_3857_; 
lean_dec_ref(v_e_3831_);
v_arg_3855_ = lean_ctor_get(v___x_3848_, 1);
lean_inc_ref(v_arg_3855_);
lean_dec_ref(v___x_3848_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 1, v_arg_3855_);
lean_ctor_set(v___x_3846_, 0, v_usedFields_3830_);
v___x_3857_ = v___x_3846_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_usedFields_3830_);
lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_arg_3855_);
v___x_3857_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
v___x_3859_ = lean_apply_2(v_toPure_3834_, lean_box(0), v___x_3858_);
return v___x_3859_;
}
}
}
}
}
}
v___jp_3835_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v_usedFields_3830_);
lean_ctor_set(v___x_3836_, 1, v_e_3831_);
v___x_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
v___x_3838_ = lean_apply_2(v_toPure_3834_, lean_box(0), v___x_3837_);
return v___x_3838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(lean_object* v_toPure_3864_, lean_object* v_usedFields_3865_, lean_object* v_binderName_3866_, lean_object* v_body_3867_, lean_object* v_val_3868_, lean_object* v_inst_3869_, lean_object* v_inst_3870_, lean_object* v_fieldVal_x3f_3871_, uint8_t v_____do__lift_3872_){
_start:
{
if (v_____do__lift_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v_fieldVal_x3f_3871_);
lean_dec(v_inst_3870_);
lean_dec_ref(v_inst_3869_);
lean_dec(v_binderName_3866_);
lean_dec(v_usedFields_3865_);
v___x_3873_ = lean_box(0);
v___x_3874_ = lean_apply_2(v_toPure_3864_, lean_box(0), v___x_3873_);
return v___x_3874_;
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_dec(v_toPure_3864_);
v___x_3875_ = l_Lean_NameSet_insert(v_usedFields_3865_, v_binderName_3866_);
v___x_3876_ = lean_expr_instantiate1(v_body_3867_, v_val_3868_);
v___x_3877_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3869_, v_inst_3870_, v_fieldVal_x3f_3871_, v___x_3875_, v___x_3876_);
return v___x_3877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(lean_object* v_m_3878_, lean_object* v_inst_3879_, lean_object* v_inst_3880_, lean_object* v_fieldVal_x3f_3881_, lean_object* v_usedFields_3882_, lean_object* v_e_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3879_, v_inst_3880_, v_fieldVal_x3f_3881_, v_usedFields_3882_, v_e_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(lean_object* v_inst_3885_, lean_object* v_inst_3886_, lean_object* v_fieldVal_x3f_3887_, lean_object* v_toPure_3888_, lean_object* v_____s_3889_){
_start:
{
lean_object* v_fst_3890_; 
v_fst_3890_ = lean_ctor_get(v_____s_3889_, 0);
if (lean_obj_tag(v_fst_3890_) == 0)
{
lean_object* v_snd_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_dec(v_toPure_3888_);
v_snd_3891_ = lean_ctor_get(v_____s_3889_, 1);
lean_inc(v_snd_3891_);
lean_dec_ref(v_____s_3889_);
v___x_3892_ = l_Lean_NameSet_empty;
v___x_3893_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_3885_, v_inst_3886_, v_fieldVal_x3f_3887_, v___x_3892_, v_snd_3891_);
return v___x_3893_;
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3895_; 
lean_inc_ref(v_fst_3890_);
lean_dec_ref(v_____s_3889_);
lean_dec(v_fieldVal_x3f_3887_);
lean_dec(v_inst_3886_);
lean_dec_ref(v_inst_3885_);
v_val_3894_ = lean_ctor_get(v_fst_3890_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v_fst_3890_, 1);
v___x_3895_ = lean_apply_2(v_toPure_3888_, lean_box(0), v_val_3894_);
return v___x_3895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3896_, lean_object* v_a_3897_, lean_object* v___x_3898_, lean_object* v_toPure_3899_, lean_object* v_____r_3900_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3901_ = lean_expr_instantiate1(v_body_3896_, v_a_3897_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3898_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
v___x_3904_ = lean_apply_2(v_toPure_3899_, lean_box(0), v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3905_, lean_object* v_a_3906_, lean_object* v___x_3907_, lean_object* v_toPure_3908_, lean_object* v_____r_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3905_, v_a_3906_, v___x_3907_, v_toPure_3908_, v_____r_3909_);
lean_dec_ref(v_a_3906_);
lean_dec_ref(v_body_3905_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3913_, lean_object* v_toPure_3914_, lean_object* v___f_3915_, uint8_t v_____do__lift_3916_){
_start:
{
if (v_____do__lift_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec(v___f_3915_);
v___x_3917_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v_snd_3913_);
v___x_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
v___x_3920_ = lean_apply_2(v_toPure_3914_, lean_box(0), v___x_3919_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec(v_toPure_3914_);
lean_dec(v_snd_3913_);
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_apply_1(v___f_3915_, v___x_3921_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3923_, lean_object* v_toPure_3924_, lean_object* v___f_3925_, lean_object* v_____do__lift_3926_){
_start:
{
uint8_t v_____do__lift_566__boxed_3927_; lean_object* v_res_3928_; 
v_____do__lift_566__boxed_3927_ = lean_unbox(v_____do__lift_3926_);
v_res_3928_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3923_, v_toPure_3924_, v___f_3925_, v_____do__lift_566__boxed_3927_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3929_, lean_object* v_inst_3930_, lean_object* v_toBind_3931_, lean_object* v___f_3932_, lean_object* v_____do__lift_3933_){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3934_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3934_, 0, v_____do__lift_3933_);
lean_closure_set(v___x_3934_, 1, v_binderType_3929_);
v___x_3935_ = lean_apply_2(v_inst_3930_, lean_box(0), v___x_3934_);
v___x_3936_ = lean_apply_4(v_toBind_3931_, lean_box(0), lean_box(0), v___x_3935_, v___f_3932_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3937_, lean_object* v_toPure_3938_, lean_object* v_levels_x3f_3939_, lean_object* v_inst_3940_, lean_object* v_toBind_3941_, lean_object* v_a_3942_, lean_object* v_x_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v_snd_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3965_; 
v_snd_3945_ = lean_ctor_get(v___y_3944_, 1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___y_3944_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v___y_3944_, 0);
lean_dec(v_unused_3966_);
v___x_3947_ = v___y_3944_;
v_isShared_3948_ = v_isSharedCheck_3965_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_snd_3945_);
lean_dec(v___y_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3965_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
if (lean_obj_tag(v_snd_3945_) == 6)
{
lean_object* v_binderType_3949_; lean_object* v_body_3950_; lean_object* v___f_3951_; 
lean_del_object(v___x_3947_);
v_binderType_3949_ = lean_ctor_get(v_snd_3945_, 1);
lean_inc_ref(v_binderType_3949_);
v_body_3950_ = lean_ctor_get(v_snd_3945_, 2);
lean_inc(v_toPure_3938_);
lean_inc(v___x_3937_);
lean_inc_ref(v_a_3942_);
lean_inc_ref(v_body_3950_);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3951_, 0, v_body_3950_);
lean_closure_set(v___f_3951_, 1, v_a_3942_);
lean_closure_set(v___f_3951_, 2, v___x_3937_);
lean_closure_set(v___f_3951_, 3, v_toPure_3938_);
if (lean_obj_tag(v_levels_x3f_3939_) == 0)
{
lean_object* v___f_3952_; lean_object* v___f_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec(v___x_3937_);
v___f_3952_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3952_, 0, v_snd_3945_);
lean_closure_set(v___f_3952_, 1, v_toPure_3938_);
lean_closure_set(v___f_3952_, 2, v___f_3951_);
lean_inc(v_toBind_3941_);
lean_inc(v_inst_3940_);
v___f_3953_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3953_, 0, v_binderType_3949_);
lean_closure_set(v___f_3953_, 1, v_inst_3940_);
lean_closure_set(v___f_3953_, 2, v_toBind_3941_);
lean_closure_set(v___f_3953_, 3, v___f_3952_);
v___x_3954_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3954_, 0, v_a_3942_);
v___x_3955_ = lean_apply_2(v_inst_3940_, lean_box(0), v___x_3954_);
v___x_3956_ = lean_apply_4(v_toBind_3941_, lean_box(0), lean_box(0), v___x_3955_, v___f_3953_);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
lean_inc_ref(v_body_3950_);
lean_dec_ref(v___f_3951_);
lean_dec_ref_known(v_snd_3945_, 3);
lean_dec_ref(v_binderType_3949_);
lean_dec(v_toBind_3941_);
lean_dec(v_inst_3940_);
v___x_3957_ = lean_box(0);
v___x_3958_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3950_, v_a_3942_, v___x_3937_, v_toPure_3938_, v___x_3957_);
lean_dec_ref(v_a_3942_);
lean_dec_ref(v_body_3950_);
return v___x_3958_;
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
lean_dec_ref(v_a_3942_);
lean_dec(v_toBind_3941_);
lean_dec(v_inst_3940_);
lean_dec(v___x_3937_);
v___x_3959_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3959_);
v___x_3961_ = v___x_3947_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_snd_3945_);
v___x_3961_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = lean_apply_2(v_toPure_3938_, lean_box(0), v___x_3962_);
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3967_, lean_object* v_toPure_3968_, lean_object* v_levels_x3f_3969_, lean_object* v_inst_3970_, lean_object* v_toBind_3971_, lean_object* v_a_3972_, lean_object* v_x_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3967_, v_toPure_3968_, v_levels_x3f_3969_, v_inst_3970_, v_toBind_3971_, v_a_3972_, v_x_3973_, v___y_3974_);
lean_dec(v_levels_x3f_3969_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3976_, lean_object* v_levels_x3f_3977_, lean_object* v_inst_3978_, lean_object* v_toBind_3979_, lean_object* v_params_3980_, lean_object* v_inst_3981_, lean_object* v___f_3982_, lean_object* v_val_3983_){
_start:
{
lean_object* v___x_3984_; lean_object* v___f_3985_; lean_object* v___x_3986_; size_t v_sz_3987_; size_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3984_ = lean_box(0);
lean_inc(v_toBind_3979_);
v___f_3985_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3985_, 0, v___x_3984_);
lean_closure_set(v___f_3985_, 1, v_toPure_3976_);
lean_closure_set(v___f_3985_, 2, v_levels_x3f_3977_);
lean_closure_set(v___f_3985_, 3, v_inst_3978_);
lean_closure_set(v___f_3985_, 4, v_toBind_3979_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v_val_3983_);
v_sz_3987_ = lean_array_size(v_params_3980_);
v___x_3988_ = ((size_t)0ULL);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3981_, v_params_3980_, v___f_3985_, v_sz_3987_, v___x_3988_, v___x_3986_);
v___x_3990_ = lean_apply_4(v_toBind_3979_, lean_box(0), lean_box(0), v___x_3989_, v___f_3982_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3991_, lean_object* v_us_3992_, uint8_t v___x_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3991_, v_us_3992_, v___x_3993_, v___y_3996_, v___y_3997_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_4000_, lean_object* v_us_4001_, lean_object* v___x_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
uint8_t v___x_677__boxed_4008_; lean_object* v_res_4009_; 
v___x_677__boxed_4008_ = lean_unbox(v___x_4002_);
v_res_4009_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_4000_, v_us_4001_, v___x_677__boxed_4008_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec_ref(v_cinfo_4000_);
return v_res_4009_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4013_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4014_ = lean_unsigned_to_nat(2u);
v___x_4015_ = lean_unsigned_to_nat(202u);
v___x_4016_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4017_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4018_ = l_mkPanicMessageWithDecl(v___x_4017_, v___x_4016_, v___x_4015_, v___x_4014_, v___x_4013_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4019_, lean_object* v___x_4020_, lean_object* v_inst_4021_, lean_object* v_toBind_4022_, lean_object* v___f_4023_, lean_object* v_us_4024_){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4025_ = l_List_lengthTR___redArg(v_us_4024_);
v___x_4026_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4019_);
v___x_4027_ = l_List_lengthTR___redArg(v___x_4026_);
lean_dec(v___x_4026_);
v___x_4028_ = lean_nat_dec_eq(v___x_4025_, v___x_4027_);
lean_dec(v___x_4027_);
lean_dec(v___x_4025_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec(v_us_4024_);
lean_dec(v___f_4023_);
lean_dec(v_toBind_4022_);
lean_dec(v_inst_4021_);
lean_dec_ref(v_cinfo_4019_);
v___x_4029_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4030_ = l_panic___redArg(v___x_4020_, v___x_4029_);
return v___x_4030_;
}
else
{
uint8_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___f_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4031_ = 0;
v___x_4032_ = lean_box(v___x_4031_);
v___f_4033_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4033_, 0, v_cinfo_4019_);
lean_closure_set(v___f_4033_, 1, v_us_4024_);
lean_closure_set(v___f_4033_, 2, v___x_4032_);
v___x_4034_ = lean_apply_2(v_inst_4021_, lean_box(0), v___f_4033_);
v___x_4035_ = lean_apply_4(v_toBind_4022_, lean_box(0), lean_box(0), v___x_4034_, v___f_4023_);
return v___x_4035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4036_, lean_object* v___x_4037_, lean_object* v_inst_4038_, lean_object* v_toBind_4039_, lean_object* v___f_4040_, lean_object* v_us_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4036_, v___x_4037_, v_inst_4038_, v_toBind_4039_, v___f_4040_, v_us_4041_);
lean_dec(v___x_4037_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4043_, lean_object* v_inst_4044_, lean_object* v_toBind_4045_, lean_object* v___f_4046_, lean_object* v_levels_x3f_4047_, lean_object* v_toPure_4048_, lean_object* v_cinfo_4049_){
_start:
{
lean_object* v___f_4050_; 
lean_inc(v_toBind_4045_);
lean_inc(v_inst_4044_);
lean_inc_ref(v_cinfo_4049_);
v___f_4050_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4050_, 0, v_cinfo_4049_);
lean_closure_set(v___f_4050_, 1, v___x_4043_);
lean_closure_set(v___f_4050_, 2, v_inst_4044_);
lean_closure_set(v___f_4050_, 3, v_toBind_4045_);
lean_closure_set(v___f_4050_, 4, v___f_4046_);
if (lean_obj_tag(v_levels_x3f_4047_) == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
lean_dec(v_toPure_4048_);
v___x_4051_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4051_, 0, v_cinfo_4049_);
v___x_4052_ = lean_apply_2(v_inst_4044_, lean_box(0), v___x_4051_);
v___x_4053_ = lean_apply_4(v_toBind_4045_, lean_box(0), lean_box(0), v___x_4052_, v___f_4050_);
return v___x_4053_;
}
else
{
lean_object* v_val_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_dec_ref(v_cinfo_4049_);
lean_dec(v_inst_4044_);
v_val_4054_ = lean_ctor_get(v_levels_x3f_4047_, 0);
lean_inc(v_val_4054_);
lean_dec_ref_known(v_levels_x3f_4047_, 1);
v___x_4055_ = lean_apply_2(v_toPure_4048_, lean_box(0), v_val_4054_);
v___x_4056_ = lean_apply_4(v_toBind_4045_, lean_box(0), lean_box(0), v___x_4055_, v___f_4050_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4057_, lean_object* v_inst_4058_, lean_object* v_inst_4059_, lean_object* v_inst_4060_, lean_object* v_defaultFn_4061_, lean_object* v_levels_x3f_4062_, lean_object* v_params_4063_, lean_object* v_fieldVal_x3f_4064_){
_start:
{
lean_object* v_toApplicative_4065_; lean_object* v_toBind_4066_; lean_object* v_toPure_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___f_4070_; lean_object* v___f_4071_; lean_object* v___x_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; 
v_toApplicative_4065_ = lean_ctor_get(v_inst_4057_, 0);
v_toBind_4066_ = lean_ctor_get(v_inst_4057_, 1);
lean_inc_n(v_toBind_4066_, 3);
v_toPure_4067_ = lean_ctor_get(v_toApplicative_4065_, 1);
lean_inc_n(v_toPure_4067_, 3);
v___x_4068_ = lean_box(0);
lean_inc_ref_n(v_inst_4057_, 3);
v___x_4069_ = l_Lean_getConstInfo___redArg(v_inst_4057_, v_inst_4058_, v_inst_4059_, v_defaultFn_4061_);
lean_inc_n(v_inst_4060_, 2);
v___f_4070_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4070_, 0, v_inst_4057_);
lean_closure_set(v___f_4070_, 1, v_inst_4060_);
lean_closure_set(v___f_4070_, 2, v_fieldVal_x3f_4064_);
lean_closure_set(v___f_4070_, 3, v_toPure_4067_);
lean_inc(v_levels_x3f_4062_);
v___f_4071_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4071_, 0, v_toPure_4067_);
lean_closure_set(v___f_4071_, 1, v_levels_x3f_4062_);
lean_closure_set(v___f_4071_, 2, v_inst_4060_);
lean_closure_set(v___f_4071_, 3, v_toBind_4066_);
lean_closure_set(v___f_4071_, 4, v_params_4063_);
lean_closure_set(v___f_4071_, 5, v_inst_4057_);
lean_closure_set(v___f_4071_, 6, v___f_4070_);
v___x_4072_ = l_instInhabitedOfMonad___redArg(v_inst_4057_, v___x_4068_);
v___f_4073_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4073_, 0, v___x_4072_);
lean_closure_set(v___f_4073_, 1, v_inst_4060_);
lean_closure_set(v___f_4073_, 2, v_toBind_4066_);
lean_closure_set(v___f_4073_, 3, v___f_4071_);
lean_closure_set(v___f_4073_, 4, v_levels_x3f_4062_);
lean_closure_set(v___f_4073_, 5, v_toPure_4067_);
v___x_4074_ = lean_apply_4(v_toBind_4066_, lean_box(0), lean_box(0), v___x_4069_, v___f_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4075_, lean_object* v_inst_4076_, lean_object* v_inst_4077_, lean_object* v_inst_4078_, lean_object* v_inst_4079_, lean_object* v_inst_4080_, lean_object* v_defaultFn_4081_, lean_object* v_levels_x3f_4082_, lean_object* v_params_4083_, lean_object* v_fieldVal_x3f_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4076_, v_inst_4077_, v_inst_4078_, v_inst_4079_, v_defaultFn_4081_, v_levels_x3f_4082_, v_params_4083_, v_fieldVal_x3f_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4086_, lean_object* v_inst_4087_, lean_object* v_inst_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_inst_4091_, lean_object* v_defaultFn_4092_, lean_object* v_levels_x3f_4093_, lean_object* v_params_4094_, lean_object* v_fieldVal_x3f_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4086_, v_inst_4087_, v_inst_4088_, v_inst_4089_, v_inst_4090_, v_inst_4091_, v_defaultFn_4092_, v_levels_x3f_4093_, v_params_4094_, v_fieldVal_x3f_4095_);
lean_dec_ref(v_inst_4091_);
return v_res_4096_;
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
