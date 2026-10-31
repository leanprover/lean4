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
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__0);
v___x_498_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
v___x_499_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_497_);
lean_ctor_set(v___x_499_, 3, v___x_497_);
lean_ctor_set(v___x_499_, 4, v___x_497_);
lean_ctor_set(v___x_499_, 5, v___x_497_);
lean_ctor_set(v___x_499_, 6, v___x_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(lean_object* v_x_500_, uint8_t v_isExporting_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v___x_509_; uint8_t v_isModule_510_; 
v___x_507_ = lean_st_ref_get(v___y_505_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_507_);
v___x_509_ = l_Lean_Environment_header(v_env_508_);
v_isModule_510_ = lean_ctor_get_uint8(v___x_509_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_509_);
if (v_isModule_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v_env_508_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v___x_511_ = lean_apply_5(v_x_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_511_;
}
else
{
uint8_t v_isExporting_512_; 
v_isExporting_512_ = lean_ctor_get_uint8(v_env_508_, sizeof(void*)*13);
lean_dec_ref(v_env_508_);
if (v_isExporting_501_ == 0)
{
if (v_isExporting_512_ == 0)
{
lean_object* v___x_579_; 
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v___x_579_ = lean_apply_5(v_x_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_579_;
}
else
{
goto v___jp_513_;
}
}
else
{
if (v_isExporting_512_ == 0)
{
goto v___jp_513_;
}
else
{
lean_object* v___x_580_; 
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v___x_580_ = lean_apply_5(v_x_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_580_;
}
}
v___jp_513_:
{
lean_object* v___x_514_; lean_object* v_env_515_; lean_object* v_nextMacroScope_516_; lean_object* v_ngen_517_; lean_object* v_auxDeclNGen_518_; lean_object* v_traceState_519_; lean_object* v_recordedDeps_520_; lean_object* v_messages_521_; lean_object* v_infoState_522_; lean_object* v_snapshotTasks_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_577_; 
v___x_514_ = lean_st_ref_take(v___y_505_);
v_env_515_ = lean_ctor_get(v___x_514_, 0);
v_nextMacroScope_516_ = lean_ctor_get(v___x_514_, 1);
v_ngen_517_ = lean_ctor_get(v___x_514_, 2);
v_auxDeclNGen_518_ = lean_ctor_get(v___x_514_, 3);
v_traceState_519_ = lean_ctor_get(v___x_514_, 4);
v_recordedDeps_520_ = lean_ctor_get(v___x_514_, 6);
v_messages_521_ = lean_ctor_get(v___x_514_, 7);
v_infoState_522_ = lean_ctor_get(v___x_514_, 8);
v_snapshotTasks_523_ = lean_ctor_get(v___x_514_, 9);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v___x_514_, 5);
lean_dec(v_unused_578_);
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_577_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snapshotTasks_523_);
lean_inc(v_infoState_522_);
lean_inc(v_messages_521_);
lean_inc(v_recordedDeps_520_);
lean_inc(v_traceState_519_);
lean_inc(v_auxDeclNGen_518_);
lean_inc(v_ngen_517_);
lean_inc(v_nextMacroScope_516_);
lean_inc(v_env_515_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_577_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = l_Lean_Environment_setExporting(v_env_515_, v_isExporting_501_);
v___x_528_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 5, v___x_528_);
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_nextMacroScope_516_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_ngen_517_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_auxDeclNGen_518_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_traceState_519_);
lean_ctor_set(v_reuseFailAlloc_576_, 5, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_576_, 6, v_recordedDeps_520_);
lean_ctor_set(v_reuseFailAlloc_576_, 7, v_messages_521_);
lean_ctor_set(v_reuseFailAlloc_576_, 8, v_infoState_522_);
lean_ctor_set(v_reuseFailAlloc_576_, 9, v_snapshotTasks_523_);
v___x_530_ = v_reuseFailAlloc_576_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_mctx_533_; lean_object* v_zetaDeltaFVarIds_534_; lean_object* v_postponed_535_; lean_object* v_diag_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_574_; 
v___x_531_ = lean_st_ref_put(v___y_505_, v___x_530_);
v___x_532_ = lean_st_ref_take(v___y_503_);
v_mctx_533_ = lean_ctor_get(v___x_532_, 0);
v_zetaDeltaFVarIds_534_ = lean_ctor_get(v___x_532_, 2);
v_postponed_535_ = lean_ctor_get(v___x_532_, 3);
v_diag_536_ = lean_ctor_get(v___x_532_, 4);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v___x_532_, 1);
lean_dec(v_unused_575_);
v___x_538_ = v___x_532_;
v_isShared_539_ = v_isSharedCheck_574_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_diag_536_);
lean_inc(v_postponed_535_);
lean_inc(v_zetaDeltaFVarIds_534_);
lean_inc(v_mctx_533_);
lean_dec(v___x_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_574_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_540_);
v___x_542_ = v___x_538_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_mctx_533_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_zetaDeltaFVarIds_534_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_postponed_535_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_diag_536_);
v___x_542_ = v_reuseFailAlloc_573_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v_r_544_; 
v___x_543_ = lean_st_ref_put(v___y_503_, v___x_542_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
v_r_544_ = lean_apply_5(v_x_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
if (lean_obj_tag(v_r_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_561_; 
v_a_545_ = lean_ctor_get(v_r_544_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v_r_544_);
if (v_isSharedCheck_561_ == 0)
{
v___x_547_ = v_r_544_;
v_isShared_548_ = v_isSharedCheck_561_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v_r_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_561_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
lean_inc(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_560_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v___x_551_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(v___y_505_, v_isExporting_512_, v___x_528_, v___y_503_, v___x_540_, v___x_550_);
lean_dec_ref(v___x_550_);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_559_);
v___x_553_ = v___x_551_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_551_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v_a_545_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_545_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_562_ = lean_ctor_get(v_r_544_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v_r_544_, 1);
v___x_563_ = lean_box(0);
v___x_564_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___lam__0(v___y_505_, v_isExporting_512_, v___x_528_, v___y_503_, v___x_540_, v___x_563_);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_564_, 0);
lean_dec(v_unused_572_);
v___x_566_ = v___x_564_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_dec(v___x_564_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 1);
lean_ctor_set(v___x_566_, 0, v_a_562_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_562_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___boxed(lean_object* v_x_581_, lean_object* v_isExporting_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v_isExporting_boxed_588_; lean_object* v_res_589_; 
v_isExporting_boxed_588_ = lean_unbox(v_isExporting_582_);
v_res_589_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_581_, v_isExporting_boxed_588_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(lean_object* v_x_590_, uint8_t v_when_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
if (v_when_591_ == 0)
{
lean_object* v___x_597_; 
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
v___x_597_ = lean_apply_5(v_x_590_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, lean_box(0));
return v___x_597_;
}
else
{
uint8_t v___x_598_; lean_object* v___x_599_; 
v___x_598_ = 0;
v___x_599_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_590_, v___x_598_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(lean_object* v_x_600_, lean_object* v_when_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_when_boxed_607_; lean_object* v_res_608_; 
v_when_boxed_607_ = lean_unbox(v_when_601_);
v_res_608_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v_x_600_, v_when_boxed_607_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(lean_object* v_ref_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_toCold_616_; lean_object* v_currRecDepth_617_; lean_object* v_ref_618_; uint16_t v_optionFlags_619_; uint8_t v_suppressElabErrors_620_; uint8_t v_checkDeprecated_621_; uint8_t v_isRecordingDeps_622_; lean_object* v_ref_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_toCold_616_ = lean_ctor_get(v___y_613_, 0);
v_currRecDepth_617_ = lean_ctor_get(v___y_613_, 1);
v_ref_618_ = lean_ctor_get(v___y_613_, 2);
v_optionFlags_619_ = lean_ctor_get_uint16(v___y_613_, sizeof(void*)*3);
v_suppressElabErrors_620_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*3 + 2);
v_checkDeprecated_621_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*3 + 3);
v_isRecordingDeps_622_ = lean_ctor_get_uint8(v___y_613_, sizeof(void*)*3 + 4);
v_ref_623_ = l_Lean_replaceRef(v_ref_609_, v_ref_618_);
lean_inc(v_currRecDepth_617_);
lean_inc_ref(v_toCold_616_);
v___x_624_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_624_, 0, v_toCold_616_);
lean_ctor_set(v___x_624_, 1, v_currRecDepth_617_);
lean_ctor_set(v___x_624_, 2, v_ref_623_);
lean_ctor_set_uint16(v___x_624_, sizeof(void*)*3, v_optionFlags_619_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*3 + 2, v_suppressElabErrors_620_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*3 + 3, v_checkDeprecated_621_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*3 + 4, v_isRecordingDeps_622_);
v___x_625_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v_msg_610_, v___y_611_, v___y_612_, v___x_624_, v___y_614_);
lean_dec_ref_known(v___x_624_, 3);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(lean_object* v_ref_626_, lean_object* v_msg_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_626_, v_msg_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v_ref_626_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(lean_object* v_declName_634_, uint8_t v_s_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_env_640_; lean_object* v_nextMacroScope_641_; lean_object* v_ngen_642_; lean_object* v_auxDeclNGen_643_; lean_object* v_traceState_644_; lean_object* v_recordedDeps_645_; lean_object* v_messages_646_; lean_object* v_infoState_647_; lean_object* v_snapshotTasks_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_677_; 
v___x_639_ = lean_st_ref_take(v___y_637_);
v_env_640_ = lean_ctor_get(v___x_639_, 0);
v_nextMacroScope_641_ = lean_ctor_get(v___x_639_, 1);
v_ngen_642_ = lean_ctor_get(v___x_639_, 2);
v_auxDeclNGen_643_ = lean_ctor_get(v___x_639_, 3);
v_traceState_644_ = lean_ctor_get(v___x_639_, 4);
v_recordedDeps_645_ = lean_ctor_get(v___x_639_, 6);
v_messages_646_ = lean_ctor_get(v___x_639_, 7);
v_infoState_647_ = lean_ctor_get(v___x_639_, 8);
v_snapshotTasks_648_ = lean_ctor_get(v___x_639_, 9);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_639_, 5);
lean_dec(v_unused_678_);
v___x_650_ = v___x_639_;
v_isShared_651_ = v_isSharedCheck_677_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_snapshotTasks_648_);
lean_inc(v_infoState_647_);
lean_inc(v_messages_646_);
lean_inc(v_recordedDeps_645_);
lean_inc(v_traceState_644_);
lean_inc(v_auxDeclNGen_643_);
lean_inc(v_ngen_642_);
lean_inc(v_nextMacroScope_641_);
lean_inc(v_env_640_);
lean_dec(v___x_639_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_677_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_652_ = 0;
v___x_653_ = lean_box(0);
v___x_654_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_640_, v_declName_634_, v_s_635_, v___x_652_, v___x_653_);
v___x_655_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 5, v___x_655_);
lean_ctor_set(v___x_650_, 0, v___x_654_);
v___x_657_ = v___x_650_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_nextMacroScope_641_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_ngen_642_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_auxDeclNGen_643_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_traceState_644_);
lean_ctor_set(v_reuseFailAlloc_676_, 5, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_676_, 6, v_recordedDeps_645_);
lean_ctor_set(v_reuseFailAlloc_676_, 7, v_messages_646_);
lean_ctor_set(v_reuseFailAlloc_676_, 8, v_infoState_647_);
lean_ctor_set(v_reuseFailAlloc_676_, 9, v_snapshotTasks_648_);
v___x_657_ = v_reuseFailAlloc_676_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_mctx_660_; lean_object* v_zetaDeltaFVarIds_661_; lean_object* v_postponed_662_; lean_object* v_diag_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_674_; 
v___x_658_ = lean_st_ref_put(v___y_637_, v___x_657_);
v___x_659_ = lean_st_ref_take(v___y_636_);
v_mctx_660_ = lean_ctor_get(v___x_659_, 0);
v_zetaDeltaFVarIds_661_ = lean_ctor_get(v___x_659_, 2);
v_postponed_662_ = lean_ctor_get(v___x_659_, 3);
v_diag_663_ = lean_ctor_get(v___x_659_, 4);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_659_, 1);
lean_dec(v_unused_675_);
v___x_665_ = v___x_659_;
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_diag_663_);
lean_inc(v_postponed_662_);
lean_inc(v_zetaDeltaFVarIds_661_);
lean_inc(v_mctx_660_);
lean_dec(v___x_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_667_ = lean_box(0);
v___x_668_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_668_);
v___x_670_ = v___x_665_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_mctx_660_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_zetaDeltaFVarIds_661_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_postponed_662_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v_diag_663_);
v___x_670_ = v_reuseFailAlloc_673_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_st_ref_put(v___y_636_, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_667_);
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg___boxed(lean_object* v_declName_679_, lean_object* v_s_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_s_boxed_684_; lean_object* v_res_685_; 
v_s_boxed_684_ = lean_unbox(v_s_680_);
v_res_685_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_679_, v_s_boxed_684_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v___y_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(lean_object* v_declName_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v___x_692_; lean_object* v___x_693_; 
v___x_692_ = 0;
v___x_693_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_686_, v___x_692_, v___y_688_, v___y_690_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6___boxed(lean_object* v_declName_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(v_declName_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_700_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__0));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__2));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__4));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__6));
v___x_712_ = l_Lean_stringToMessageData(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__8));
v___x_715_ = l_Lean_stringToMessageData(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(lean_object* v___x_716_, lean_object* v_projName_717_, lean_object* v___x_718_, lean_object* v_a_719_, uint8_t v_instImplicit_720_, lean_object* v___x_721_, lean_object* v_params_722_, lean_object* v_self_723_, lean_object* v_b_724_, uint8_t v___x_725_, lean_object* v_a_726_, lean_object* v___x_727_, lean_object* v_paramInfoOverrides_728_, lean_object* v_n_729_, lean_object* v_ref_730_, lean_object* v___x_731_, uint8_t v_a_732_, lean_object* v_____r_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = l_List_lengthTR___redArg(v_paramInfoOverrides_728_);
v___x_903_ = lean_array_get_size(v_params_722_);
v___x_904_ = lean_nat_dec_le(v___x_902_, v___x_903_);
lean_dec(v___x_902_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_905_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
lean_inc(v_projName_717_);
v___x_906_ = l_Lean_MessageData_ofName(v_projName_717_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc(v_n_729_);
v___x_910_ = l_Lean_MessageData_ofConstName(v_n_729_, v___x_904_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__9);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_730_, v___x_913_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_dec_ref_known(v___x_914_, 1);
goto v___jp_863_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___x_731_);
lean_dec(v_n_729_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
goto v___jp_863_;
}
v___jp_739_:
{
lean_object* v___x_742_; lean_object* v_env_743_; lean_object* v_nextMacroScope_744_; lean_object* v_ngen_745_; lean_object* v_auxDeclNGen_746_; lean_object* v_traceState_747_; lean_object* v_recordedDeps_748_; lean_object* v_messages_749_; lean_object* v_infoState_750_; lean_object* v_snapshotTasks_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_783_; 
v___x_742_ = lean_st_ref_take(v___y_741_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
v_nextMacroScope_744_ = lean_ctor_get(v___x_742_, 1);
v_ngen_745_ = lean_ctor_get(v___x_742_, 2);
v_auxDeclNGen_746_ = lean_ctor_get(v___x_742_, 3);
v_traceState_747_ = lean_ctor_get(v___x_742_, 4);
v_recordedDeps_748_ = lean_ctor_get(v___x_742_, 6);
v_messages_749_ = lean_ctor_get(v___x_742_, 7);
v_infoState_750_ = lean_ctor_get(v___x_742_, 8);
v_snapshotTasks_751_ = lean_ctor_get(v___x_742_, 9);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v___x_742_, 5);
lean_dec(v_unused_784_);
v___x_753_ = v___x_742_;
v_isShared_754_ = v_isSharedCheck_783_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_snapshotTasks_751_);
lean_inc(v_infoState_750_);
lean_inc(v_messages_749_);
lean_inc(v_recordedDeps_748_);
lean_inc(v_traceState_747_);
lean_inc(v_auxDeclNGen_746_);
lean_inc(v_ngen_745_);
lean_inc(v_nextMacroScope_744_);
lean_inc(v_env_743_);
lean_dec(v___x_742_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_783_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_name_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v_name_755_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_name_755_);
lean_dec_ref(v___x_716_);
lean_inc(v_projName_717_);
v___x_756_ = l_Lean_addProjectionFnInfo(v_env_743_, v_projName_717_, v_name_755_, v___x_718_, v_a_719_, v_instImplicit_720_);
v___x_757_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__1);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 5, v___x_757_);
lean_ctor_set(v___x_753_, 0, v___x_756_);
v___x_759_ = v___x_753_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_nextMacroScope_744_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_ngen_745_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_auxDeclNGen_746_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_traceState_747_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_recordedDeps_748_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_messages_749_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_infoState_750_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_snapshotTasks_751_);
v___x_759_ = v_reuseFailAlloc_782_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_mctx_762_; lean_object* v_zetaDeltaFVarIds_763_; lean_object* v_postponed_764_; lean_object* v_diag_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_780_; 
v___x_760_ = lean_st_ref_put(v___y_741_, v___x_759_);
v___x_761_ = lean_st_ref_take(v___y_740_);
v_mctx_762_ = lean_ctor_get(v___x_761_, 0);
v_zetaDeltaFVarIds_763_ = lean_ctor_get(v___x_761_, 2);
v_postponed_764_ = lean_ctor_get(v___x_761_, 3);
v_diag_765_ = lean_ctor_get(v___x_761_, 4);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_761_, 1);
lean_dec(v_unused_781_);
v___x_767_ = v___x_761_;
v_isShared_768_ = v_isSharedCheck_780_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_diag_765_);
lean_inc(v_postponed_764_);
lean_inc(v_zetaDeltaFVarIds_763_);
lean_inc(v_mctx_762_);
lean_dec(v___x_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_780_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__3);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_mctx_762_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_zetaDeltaFVarIds_763_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_postponed_764_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v_diag_765_);
v___x_771_ = v_reuseFailAlloc_779_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_772_ = lean_st_ref_put(v___y_740_, v___x_771_);
v___x_773_ = l_Lean_Expr_const___override(v_projName_717_, v___x_721_);
v___x_774_ = l_Lean_mkAppN(v___x_773_, v_params_722_);
v___x_775_ = l_Lean_Expr_app___override(v___x_774_, v_self_723_);
v___x_776_ = l_Lean_Expr_bindingBody_x21(v_b_724_);
v___x_777_ = lean_expr_instantiate1(v___x_776_, v___x_775_);
lean_dec_ref(v___x_775_);
lean_dec_ref(v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
}
}
v___jp_785_:
{
if (lean_obj_tag(v___y_788_) == 0)
{
lean_dec_ref_known(v___y_788_, 1);
v___y_740_ = v___y_786_;
v___y_741_ = v___y_787_;
goto v___jp_739_;
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_789_ = lean_ctor_get(v___y_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___y_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___y_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___y_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
v___jp_797_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_804_ = lean_box(0);
lean_inc(v_projName_717_);
v___x_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_805_, 0, v_projName_717_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_806_, 0, v___y_799_);
lean_ctor_set(v___x_806_, 1, v___y_803_);
lean_ctor_set(v___x_806_, 2, v___x_805_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*3, v___x_725_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_addDecl(v___x_807_, v___y_798_, v___y_801_, v___y_802_);
lean_dec_ref(v___y_801_);
v___y_786_ = v___y_800_;
v___y_787_ = v___y_802_;
v___y_788_ = v___x_808_;
goto v___jp_785_;
}
v___jp_809_:
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v_toCold_818_; lean_object* v_currRecDepth_819_; lean_object* v_ref_820_; uint16_t v_optionFlags_821_; uint8_t v_suppressElabErrors_822_; uint8_t v_checkDeprecated_823_; uint8_t v_isRecordingDeps_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_ref_829_; lean_object* v___x_830_; 
v___x_816_ = 0;
lean_inc_ref(v_a_726_);
v___x_817_ = l_Lean_LocalContext_mkForall(v_a_726_, v___x_727_, v___y_811_, v___x_725_, v___x_816_);
lean_dec_ref(v___y_811_);
v_toCold_818_ = lean_ctor_get(v___y_814_, 0);
v_currRecDepth_819_ = lean_ctor_get(v___y_814_, 1);
v_ref_820_ = lean_ctor_get(v___y_814_, 2);
v_optionFlags_821_ = lean_ctor_get_uint16(v___y_814_, sizeof(void*)*3);
v_suppressElabErrors_822_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 2);
v_checkDeprecated_823_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 3);
v_isRecordingDeps_824_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 4);
v___x_825_ = l_Lean_Expr_inferImplicit(v___x_817_, v___x_718_, v___x_725_);
v___x_826_ = l_Lean_Expr_updateForallBinderInfos(v___x_825_, v_paramInfoOverrides_728_);
lean_inc_ref(v_self_723_);
lean_inc(v_a_719_);
v___x_827_ = l_Lean_Expr_proj___override(v_n_729_, v_a_719_, v_self_723_);
v___x_828_ = l_Lean_LocalContext_mkLambda(v_a_726_, v___x_727_, v___x_827_, v___x_725_, v___x_816_);
lean_dec_ref(v___x_827_);
v_ref_829_ = l_Lean_replaceRef(v_ref_730_, v_ref_820_);
lean_inc(v_currRecDepth_819_);
lean_inc_ref(v_toCold_818_);
v___x_830_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_830_, 0, v_toCold_818_);
lean_ctor_set(v___x_830_, 1, v_currRecDepth_819_);
lean_ctor_set(v___x_830_, 2, v_ref_829_);
lean_ctor_set_uint16(v___x_830_, sizeof(void*)*3, v_optionFlags_821_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 2, v_suppressElabErrors_822_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 3, v_checkDeprecated_823_);
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*3 + 4, v_isRecordingDeps_824_);
if (v___y_810_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(1);
lean_inc(v_projName_717_);
v___x_832_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__5___redArg(v_projName_717_, v___x_731_, v___x_826_, v___x_828_, v___x_831_, v___y_815_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_a_833_);
v___x_835_ = l_Lean_addDecl(v___x_834_, v___x_816_, v___x_830_, v___y_815_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_dec_ref_known(v___x_835_, 1);
if (v_instImplicit_720_ == 0)
{
lean_object* v___x_836_; 
lean_inc(v_projName_717_);
v___x_836_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6(v_projName_717_, v___y_812_, v___y_813_, v___x_830_, v___y_815_);
lean_dec_ref_known(v___x_830_, 3);
v___y_786_ = v___y_813_;
v___y_787_ = v___y_815_;
v___y_788_ = v___x_836_;
goto v___jp_785_;
}
else
{
lean_dec_ref_known(v___x_830_, 3);
v___y_740_ = v___y_813_;
v___y_741_ = v___y_815_;
goto v___jp_739_;
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_837_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref_known(v___x_830_, 3);
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_845_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_832_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_env_855_; uint8_t v___x_856_; 
lean_inc_ref(v___x_826_);
lean_inc(v_projName_717_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v_projName_717_);
lean_ctor_set(v___x_853_, 1, v___x_731_);
lean_ctor_set(v___x_853_, 2, v___x_826_);
v___x_854_ = lean_st_ref_get(v___y_815_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref_n(v_env_855_, 2);
lean_dec(v___x_854_);
v___x_856_ = l_Lean_Environment_hasUnsafe(v_env_855_, v___x_826_);
lean_dec_ref(v___x_826_);
if (v___x_856_ == 0)
{
uint8_t v___x_857_; 
v___x_857_ = l_Lean_Environment_hasUnsafe(v_env_855_, v___x_828_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_858_ = lean_box(0);
lean_inc(v_projName_717_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v_projName_717_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v___x_853_);
lean_ctor_set(v___x_860_, 1, v___x_828_);
lean_ctor_set(v___x_860_, 2, v___x_859_);
v___x_861_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
v___x_862_ = l_Lean_addDecl(v___x_861_, v___x_816_, v___x_830_, v___y_815_);
lean_dec_ref_known(v___x_830_, 3);
v___y_786_ = v___y_813_;
v___y_787_ = v___y_815_;
v___y_788_ = v___x_862_;
goto v___jp_785_;
}
else
{
v___y_798_ = v___x_816_;
v___y_799_ = v___x_853_;
v___y_800_ = v___y_813_;
v___y_801_ = v___x_830_;
v___y_802_ = v___y_815_;
v___y_803_ = v___x_828_;
goto v___jp_797_;
}
}
else
{
lean_dec_ref(v_env_855_);
v___y_798_ = v___x_816_;
v___y_799_ = v___x_853_;
v___y_800_ = v___y_813_;
v___y_801_ = v___x_830_;
v___y_802_ = v___y_815_;
v___y_803_ = v___x_828_;
goto v___jp_797_;
}
}
}
v___jp_863_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = l_Lean_Expr_bindingDomain_x21(v_b_724_);
v___x_865_ = lean_expr_consume_type_annotations(v___x_864_);
lean_inc_ref(v___x_865_);
v___x_866_ = l_Lean_Meta_isProp(v___x_865_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_866_) == 0)
{
if (v_a_732_ == 0)
{
lean_object* v_a_867_; uint8_t v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
v___y_810_ = v___x_868_;
v___y_811_ = v___x_865_;
v___y_812_ = v___y_734_;
v___y_813_ = v___y_735_;
v___y_814_ = v___y_736_;
v___y_815_ = v___y_737_;
goto v___jp_809_;
}
else
{
lean_object* v_a_869_; uint8_t v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_866_, 1);
v___x_870_ = lean_unbox(v_a_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_871_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
lean_inc(v_projName_717_);
v___x_872_ = l_Lean_MessageData_ofName(v_projName_717_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__3);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_unbox(v_a_869_);
lean_inc(v_n_729_);
v___x_877_ = l_Lean_MessageData_ofConstName(v_n_729_, v___x_876_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__5);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_inc_ref(v___x_865_);
v___x_881_ = l_Lean_indentExpr(v___x_865_);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_730_, v___x_882_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_883_) == 0)
{
uint8_t v___x_884_; 
lean_dec_ref_known(v___x_883_, 1);
v___x_884_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___y_810_ = v___x_884_;
v___y_811_ = v___x_865_;
v___y_812_ = v___y_734_;
v___y_813_ = v___y_735_;
v___y_814_ = v___y_736_;
v___y_815_ = v___y_737_;
goto v___jp_809_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_869_);
lean_dec_ref(v___x_865_);
lean_dec(v___x_731_);
lean_dec(v_n_729_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_885_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
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
else
{
uint8_t v___x_893_; 
v___x_893_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___y_810_ = v___x_893_;
v___y_811_ = v___x_865_;
v___y_812_ = v___y_734_;
v___y_813_ = v___y_735_;
v___y_814_ = v___y_736_;
v___y_815_ = v___y_737_;
goto v___jp_809_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_865_);
lean_dec(v___x_731_);
lean_dec(v_n_729_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v_self_723_);
lean_dec(v___x_721_);
lean_dec(v_a_719_);
lean_dec(v___x_718_);
lean_dec(v_projName_717_);
lean_dec_ref(v___x_716_);
v_a_894_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_866_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_866_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_923_ = _args[0];
lean_object* v_projName_924_ = _args[1];
lean_object* v___x_925_ = _args[2];
lean_object* v_a_926_ = _args[3];
lean_object* v_instImplicit_927_ = _args[4];
lean_object* v___x_928_ = _args[5];
lean_object* v_params_929_ = _args[6];
lean_object* v_self_930_ = _args[7];
lean_object* v_b_931_ = _args[8];
lean_object* v___x_932_ = _args[9];
lean_object* v_a_933_ = _args[10];
lean_object* v___x_934_ = _args[11];
lean_object* v_paramInfoOverrides_935_ = _args[12];
lean_object* v_n_936_ = _args[13];
lean_object* v_ref_937_ = _args[14];
lean_object* v___x_938_ = _args[15];
lean_object* v_a_939_ = _args[16];
lean_object* v_____r_940_ = _args[17];
lean_object* v___y_941_ = _args[18];
lean_object* v___y_942_ = _args[19];
lean_object* v___y_943_ = _args[20];
lean_object* v___y_944_ = _args[21];
lean_object* v___y_945_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_946_; uint8_t v___x_17912__boxed_947_; uint8_t v_a_17918__boxed_948_; lean_object* v_res_949_; 
v_instImplicit_boxed_946_ = lean_unbox(v_instImplicit_927_);
v___x_17912__boxed_947_ = lean_unbox(v___x_932_);
v_a_17918__boxed_948_ = lean_unbox(v_a_939_);
v_res_949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(v___x_923_, v_projName_924_, v___x_925_, v_a_926_, v_instImplicit_boxed_946_, v___x_928_, v_params_929_, v_self_930_, v_b_931_, v___x_17912__boxed_947_, v_a_933_, v___x_934_, v_paramInfoOverrides_935_, v_n_936_, v_ref_937_, v___x_938_, v_a_17918__boxed_948_, v_____r_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v_ref_937_);
lean_dec(v_paramInfoOverrides_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v_b_931_);
lean_dec_ref(v_params_929_);
return v_res_949_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__0));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(uint8_t v___x_953_, lean_object* v_projName_954_, lean_object* v_n_955_, lean_object* v_ref_956_, lean_object* v___f_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
if (v___x_953_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_963_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__1);
v___x_964_ = l_Lean_MessageData_ofName(v_projName_954_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___closed__7);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_MessageData_ofConstName(v_n_955_, v___x_953_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___closed__1);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_956_, v___x_971_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
v___x_974_ = lean_apply_6(v___f_957_, v_a_973_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, lean_box(0));
return v___x_974_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___f_957_);
v_a_975_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_972_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_n_955_);
lean_dec(v_projName_954_);
v___x_983_ = lean_box(0);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
lean_inc(v___y_959_);
lean_inc_ref(v___y_958_);
v___x_984_ = lean_apply_6(v___f_957_, v___x_983_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, lean_box(0));
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___boxed(lean_object* v___x_985_, lean_object* v_projName_986_, lean_object* v_n_987_, lean_object* v_ref_988_, lean_object* v___f_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v___x_18311__boxed_995_; lean_object* v_res_996_; 
v___x_18311__boxed_995_ = lean_unbox(v___x_985_);
v_res_996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1(v___x_18311__boxed_995_, v_projName_986_, v_n_987_, v_ref_988_, v___f_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v_ref_988_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(lean_object* v_upperBound_997_, lean_object* v_projDecls_998_, lean_object* v___x_999_, lean_object* v___x_1000_, uint8_t v_instImplicit_1001_, lean_object* v___x_1002_, lean_object* v_params_1003_, lean_object* v_self_1004_, lean_object* v_a_1005_, lean_object* v___x_1006_, lean_object* v_n_1007_, lean_object* v___x_1008_, uint8_t v_a_1009_, lean_object* v_a_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_nat_dec_lt(v_a_1010_, v_upperBound_997_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec(v_n_1007_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v_a_1005_);
lean_dec_ref(v_self_1004_);
lean_dec_ref(v_params_1003_);
lean_dec(v___x_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_999_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1011_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_ref_1020_; lean_object* v_projName_1021_; lean_object* v_paramInfoOverrides_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___y_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1019_ = lean_array_fget_borrowed(v_projDecls_998_, v_a_1010_);
v_ref_1020_ = lean_ctor_get(v___x_1019_, 0);
v_projName_1021_ = lean_ctor_get(v___x_1019_, 1);
v_paramInfoOverrides_1022_ = lean_ctor_get(v___x_1019_, 2);
v___x_1023_ = lean_box(v_instImplicit_1001_);
v___x_1024_ = lean_box(v___x_1017_);
v___x_1025_ = lean_box(v_a_1009_);
lean_inc(v___x_1008_);
lean_inc_n(v_ref_1020_, 2);
lean_inc_n(v_n_1007_, 2);
lean_inc(v_paramInfoOverrides_1022_);
lean_inc_ref(v___x_1006_);
lean_inc_ref(v_a_1005_);
lean_inc_ref(v_b_1011_);
lean_inc_ref(v_self_1004_);
lean_inc_ref(v_params_1003_);
lean_inc(v___x_1002_);
lean_inc(v_a_1010_);
lean_inc(v___x_1000_);
lean_inc_n(v_projName_1021_, 2);
lean_inc_ref(v___x_999_);
v___f_1026_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed), 23, 17);
lean_closure_set(v___f_1026_, 0, v___x_999_);
lean_closure_set(v___f_1026_, 1, v_projName_1021_);
lean_closure_set(v___f_1026_, 2, v___x_1000_);
lean_closure_set(v___f_1026_, 3, v_a_1010_);
lean_closure_set(v___f_1026_, 4, v___x_1023_);
lean_closure_set(v___f_1026_, 5, v___x_1002_);
lean_closure_set(v___f_1026_, 6, v_params_1003_);
lean_closure_set(v___f_1026_, 7, v_self_1004_);
lean_closure_set(v___f_1026_, 8, v_b_1011_);
lean_closure_set(v___f_1026_, 9, v___x_1024_);
lean_closure_set(v___f_1026_, 10, v_a_1005_);
lean_closure_set(v___f_1026_, 11, v___x_1006_);
lean_closure_set(v___f_1026_, 12, v_paramInfoOverrides_1022_);
lean_closure_set(v___f_1026_, 13, v_n_1007_);
lean_closure_set(v___f_1026_, 14, v_ref_1020_);
lean_closure_set(v___f_1026_, 15, v___x_1008_);
lean_closure_set(v___f_1026_, 16, v___x_1025_);
v___x_1027_ = l_Lean_Expr_isForall(v_b_1011_);
lean_dec_ref(v_b_1011_);
v___x_1028_ = lean_box(v___x_1027_);
v___y_1029_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__1___boxed), 10, 5);
lean_closure_set(v___y_1029_, 0, v___x_1028_);
lean_closure_set(v___y_1029_, 1, v_projName_1021_);
lean_closure_set(v___y_1029_, 2, v_n_1007_);
lean_closure_set(v___y_1029_, 3, v_ref_1020_);
lean_closure_set(v___y_1029_, 4, v___f_1026_);
v___x_1030_ = l_Lean_isPrivateName(v_projName_1021_);
v___x_1031_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v___y_1029_, v___x_1030_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_unsigned_to_nat(1u);
v___x_1034_ = lean_nat_add(v_a_1010_, v___x_1033_);
lean_dec(v_a_1010_);
v_a_1010_ = v___x_1034_;
v_b_1011_ = v_a_1032_;
goto _start;
}
else
{
lean_dec(v_a_1010_);
lean_dec(v___x_1008_);
lean_dec(v_n_1007_);
lean_dec_ref(v___x_1006_);
lean_dec_ref(v_a_1005_);
lean_dec_ref(v_self_1004_);
lean_dec_ref(v_params_1003_);
lean_dec(v___x_1002_);
lean_dec(v___x_1000_);
lean_dec_ref(v___x_999_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1036_ = _args[0];
lean_object* v_projDecls_1037_ = _args[1];
lean_object* v___x_1038_ = _args[2];
lean_object* v___x_1039_ = _args[3];
lean_object* v_instImplicit_1040_ = _args[4];
lean_object* v___x_1041_ = _args[5];
lean_object* v_params_1042_ = _args[6];
lean_object* v_self_1043_ = _args[7];
lean_object* v_a_1044_ = _args[8];
lean_object* v___x_1045_ = _args[9];
lean_object* v_n_1046_ = _args[10];
lean_object* v___x_1047_ = _args[11];
lean_object* v_a_1048_ = _args[12];
lean_object* v_a_1049_ = _args[13];
lean_object* v_b_1050_ = _args[14];
lean_object* v___y_1051_ = _args[15];
lean_object* v___y_1052_ = _args[16];
lean_object* v___y_1053_ = _args[17];
lean_object* v___y_1054_ = _args[18];
lean_object* v___y_1055_ = _args[19];
_start:
{
uint8_t v_instImplicit_boxed_1056_; uint8_t v_a_18392__boxed_1057_; lean_object* v_res_1058_; 
v_instImplicit_boxed_1056_ = lean_unbox(v_instImplicit_1040_);
v_a_18392__boxed_1057_ = lean_unbox(v_a_1048_);
v_res_1058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v_upperBound_1036_, v_projDecls_1037_, v___x_1038_, v___x_1039_, v_instImplicit_boxed_1056_, v___x_1041_, v_params_1042_, v_self_1043_, v_a_1044_, v___x_1045_, v_n_1046_, v___x_1047_, v_a_18392__boxed_1057_, v_a_1049_, v_b_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_projDecls_1037_);
lean_dec(v_upperBound_1036_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0(lean_object* v_params_1059_, uint8_t v_instImplicit_1060_, lean_object* v_projDecls_1061_, lean_object* v_toConstantVal_1062_, lean_object* v_numParams_1063_, lean_object* v___x_1064_, lean_object* v_n_1065_, lean_object* v_levelParams_1066_, uint8_t v_a_1067_, lean_object* v_ctorType_1068_, lean_object* v_self_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_lctx_1075_; lean_object* v___x_1076_; size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_1079_; 
v_lctx_1075_ = lean_ctor_get(v___y_1070_, 2);
lean_inc_ref(v_self_1069_);
lean_inc_ref(v_params_1059_);
v___x_1076_ = lean_array_push(v_params_1059_, v_self_1069_);
v_sz_1077_ = lean_array_size(v_params_1059_);
v___x_1078_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_1075_);
v___x_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1060_, v_params_1059_, v_sz_1077_, v___x_1078_, v_lctx_1075_, v___y_1070_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_array_get_size(v_projDecls_1061_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v___x_1081_, v_projDecls_1061_, v_toConstantVal_1062_, v_numParams_1063_, v_instImplicit_1060_, v___x_1064_, v_params_1059_, v_self_1069_, v_a_1080_, v___x_1076_, v_n_1065_, v_levelParams_1066_, v_a_1067_, v___x_1082_, v_ctorType_1068_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1092_);
v___x_1085_ = v___x_1083_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v___x_1083_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(0);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1083_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1083_);
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
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_self_1069_);
lean_dec_ref(v_ctorType_1068_);
lean_dec(v_levelParams_1066_);
lean_dec(v_n_1065_);
lean_dec(v___x_1064_);
lean_dec(v_numParams_1063_);
lean_dec_ref(v_toConstantVal_1062_);
lean_dec_ref(v_params_1059_);
v_a_1101_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1079_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1079_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__0___boxed(lean_object* v_params_1109_, lean_object* v_instImplicit_1110_, lean_object* v_projDecls_1111_, lean_object* v_toConstantVal_1112_, lean_object* v_numParams_1113_, lean_object* v___x_1114_, lean_object* v_n_1115_, lean_object* v_levelParams_1116_, lean_object* v_a_1117_, lean_object* v_ctorType_1118_, lean_object* v_self_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v_instImplicit_boxed_1125_; uint8_t v_a_18464__boxed_1126_; lean_object* v_res_1127_; 
v_instImplicit_boxed_1125_ = lean_unbox(v_instImplicit_1110_);
v_a_18464__boxed_1126_ = lean_unbox(v_a_1117_);
v_res_1127_ = l_Lean_Meta_mkProjections___lam__0(v_params_1109_, v_instImplicit_boxed_1125_, v_projDecls_1111_, v_toConstantVal_1112_, v_numParams_1113_, v___x_1114_, v_n_1115_, v_levelParams_1116_, v_a_18464__boxed_1126_, v_ctorType_1118_, v_self_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec_ref(v_projDecls_1111_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__2));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__4));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1(uint8_t v_instImplicit_1137_, lean_object* v_projDecls_1138_, lean_object* v_toConstantVal_1139_, lean_object* v_numParams_1140_, lean_object* v___x_1141_, lean_object* v_n_1142_, lean_object* v_levelParams_1143_, uint8_t v_a_1144_, lean_object* v_params_1145_, lean_object* v_ctorType_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___y_1159_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1163_ = lean_box(v_instImplicit_1137_);
v___x_1164_ = lean_box(v_a_1144_);
lean_inc(v_n_1142_);
lean_inc(v___x_1141_);
lean_inc(v_numParams_1140_);
lean_inc_ref(v_params_1145_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__0___boxed), 16, 10);
lean_closure_set(v___f_1165_, 0, v_params_1145_);
lean_closure_set(v___f_1165_, 1, v___x_1163_);
lean_closure_set(v___f_1165_, 2, v_projDecls_1138_);
lean_closure_set(v___f_1165_, 3, v_toConstantVal_1139_);
lean_closure_set(v___f_1165_, 4, v_numParams_1140_);
lean_closure_set(v___f_1165_, 5, v___x_1141_);
lean_closure_set(v___f_1165_, 6, v_n_1142_);
lean_closure_set(v___f_1165_, 7, v_levelParams_1143_);
lean_closure_set(v___f_1165_, 8, v___x_1164_);
lean_closure_set(v___f_1165_, 9, v_ctorType_1146_);
v___x_1171_ = lean_array_get_size(v_params_1145_);
v___x_1172_ = lean_nat_dec_eq(v___x_1171_, v_numParams_1140_);
lean_dec(v_numParams_1140_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v___f_1165_);
lean_dec_ref(v_params_1145_);
lean_dec(v___x_1141_);
v___x_1173_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__3, &l_Lean_Meta_mkProjections___lam__1___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__3);
v___x_1174_ = l_Lean_MessageData_ofConstName(v_n_1142_, v___x_1172_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__1___closed__5, &l_Lean_Meta_mkProjections___lam__1___closed__5_once, _init_l_Lean_Meta_mkProjections___lam__1___closed__5);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1177_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1178_;
}
else
{
goto v___jp_1166_;
}
v___jp_1152_:
{
lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__1___closed__1));
v___x_1161_ = 0;
v___x_1162_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__10___redArg(v___x_1160_, v___y_1159_, v___y_1156_, v___y_1154_, v___x_1161_, v___y_1153_, v___y_1155_, v___y_1158_, v___y_1157_);
return v___x_1162_;
}
v___jp_1166_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l_Lean_Expr_const___override(v_n_1142_, v___x_1141_);
v___x_1168_ = l_Lean_mkAppN(v___x_1167_, v_params_1145_);
lean_dec_ref(v_params_1145_);
if (v_instImplicit_1137_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 0;
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___f_1165_;
v___y_1155_ = v___y_1148_;
v___y_1156_ = v___x_1168_;
v___y_1157_ = v___y_1150_;
v___y_1158_ = v___y_1149_;
v___y_1159_ = v___x_1169_;
goto v___jp_1152_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 3;
v___y_1153_ = v___y_1147_;
v___y_1154_ = v___f_1165_;
v___y_1155_ = v___y_1148_;
v___y_1156_ = v___x_1168_;
v___y_1157_ = v___y_1150_;
v___y_1158_ = v___y_1149_;
v___y_1159_ = v___x_1170_;
goto v___jp_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__1___boxed(lean_object* v_instImplicit_1179_, lean_object* v_projDecls_1180_, lean_object* v_toConstantVal_1181_, lean_object* v_numParams_1182_, lean_object* v___x_1183_, lean_object* v_n_1184_, lean_object* v_levelParams_1185_, lean_object* v_a_1186_, lean_object* v_params_1187_, lean_object* v_ctorType_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v_instImplicit_boxed_1194_; uint8_t v_a_18568__boxed_1195_; lean_object* v_res_1196_; 
v_instImplicit_boxed_1194_ = lean_unbox(v_instImplicit_1179_);
v_a_18568__boxed_1195_ = lean_unbox(v_a_1186_);
v_res_1196_ = l_Lean_Meta_mkProjections___lam__1(v_instImplicit_boxed_1194_, v_projDecls_1180_, v_toConstantVal_1181_, v_numParams_1182_, v___x_1183_, v_n_1184_, v_levelParams_1185_, v_a_18568__boxed_1195_, v_params_1187_, v_ctorType_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(lean_object* v_a_1197_, lean_object* v_a_1198_){
_start:
{
if (lean_obj_tag(v_a_1197_) == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = l_List_reverse___redArg(v_a_1198_);
return v___x_1199_;
}
else
{
lean_object* v_head_1200_; lean_object* v_tail_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v_head_1200_ = lean_ctor_get(v_a_1197_, 0);
v_tail_1201_ = lean_ctor_get(v_a_1197_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1203_ = v_a_1197_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_tail_1201_);
lean_inc(v_head_1200_);
lean_dec(v_a_1197_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_mkLevelParam(v_head_1200_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_a_1198_);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1198_);
v___x_1207_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
v_a_1197_ = v_tail_1201_;
v_a_1198_ = v___x_1207_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_instMonadEIO___redArg();
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_toApplicative_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1285_; 
v___x_1222_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
v___x_1223_ = l_StateRefT_x27_instMonad___redArg(v___x_1222_);
v_toApplicative_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1223_, 1);
lean_dec(v_unused_1286_);
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1285_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_toApplicative_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1285_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_toFunctor_1228_; lean_object* v_toSeq_1229_; lean_object* v_toSeqLeft_1230_; lean_object* v_toSeqRight_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1283_; 
v_toFunctor_1228_ = lean_ctor_get(v_toApplicative_1224_, 0);
v_toSeq_1229_ = lean_ctor_get(v_toApplicative_1224_, 2);
v_toSeqLeft_1230_ = lean_ctor_get(v_toApplicative_1224_, 3);
v_toSeqRight_1231_ = lean_ctor_get(v_toApplicative_1224_, 4);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_toApplicative_1224_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_dec(v_unused_1284_);
v___x_1233_ = v_toApplicative_1224_;
v_isShared_1234_ = v_isSharedCheck_1283_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_toSeqRight_1231_);
lean_inc(v_toSeqLeft_1230_);
lean_inc(v_toSeq_1229_);
lean_inc(v_toFunctor_1228_);
lean_dec(v_toApplicative_1224_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1283_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1244_; 
v___f_1235_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1));
v___f_1236_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1228_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toFunctor_1228_);
v___f_1238_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1238_, 0, v_toFunctor_1228_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___f_1237_);
lean_ctor_set(v___x_1239_, 1, v___f_1238_);
v___f_1240_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1240_, 0, v_toSeqRight_1231_);
v___f_1241_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1241_, 0, v_toSeqLeft_1230_);
v___f_1242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1242_, 0, v_toSeq_1229_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 4, v___f_1240_);
lean_ctor_set(v___x_1233_, 3, v___f_1241_);
lean_ctor_set(v___x_1233_, 2, v___f_1242_);
lean_ctor_set(v___x_1233_, 1, v___f_1235_);
lean_ctor_set(v___x_1233_, 0, v___x_1239_);
v___x_1244_ = v___x_1233_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v___f_1242_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v___f_1241_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v___f_1240_);
v___x_1244_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___f_1236_);
lean_ctor_set(v___x_1226_, 0, v___x_1244_);
v___x_1246_ = v___x_1226_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___f_1236_);
v___x_1246_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v_toApplicative_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1279_; 
v___x_1247_ = l_StateRefT_x27_instMonad___redArg(v___x_1246_);
v_toApplicative_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1247_, 1);
lean_dec(v_unused_1280_);
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1279_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_toApplicative_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1279_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_toFunctor_1252_; lean_object* v_toSeq_1253_; lean_object* v_toSeqLeft_1254_; lean_object* v_toSeqRight_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1277_; 
v_toFunctor_1252_ = lean_ctor_get(v_toApplicative_1248_, 0);
v_toSeq_1253_ = lean_ctor_get(v_toApplicative_1248_, 2);
v_toSeqLeft_1254_ = lean_ctor_get(v_toApplicative_1248_, 3);
v_toSeqRight_1255_ = lean_ctor_get(v_toApplicative_1248_, 4);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_toApplicative_1248_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_toApplicative_1248_, 1);
lean_dec(v_unused_1278_);
v___x_1257_ = v_toApplicative_1248_;
v_isShared_1258_ = v_isSharedCheck_1277_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_toSeqRight_1255_);
lean_inc(v_toSeqLeft_1254_);
lean_inc(v_toSeq_1253_);
lean_inc(v_toFunctor_1252_);
lean_dec(v_toApplicative_1248_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1277_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___x_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1268_; 
v___f_1259_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3));
v___f_1260_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1252_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toFunctor_1252_);
v___f_1262_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1262_, 0, v_toFunctor_1252_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___f_1261_);
lean_ctor_set(v___x_1263_, 1, v___f_1262_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toSeqRight_1255_);
v___f_1265_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1265_, 0, v_toSeqLeft_1254_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toSeq_1253_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 4, v___f_1264_);
lean_ctor_set(v___x_1257_, 3, v___f_1265_);
lean_ctor_set(v___x_1257_, 2, v___f_1266_);
lean_ctor_set(v___x_1257_, 1, v___f_1259_);
lean_ctor_set(v___x_1257_, 0, v___x_1263_);
v___x_1268_ = v___x_1257_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___f_1259_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___f_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___f_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___f_1264_);
v___x_1268_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___f_1260_);
lean_ctor_set(v___x_1250_, 0, v___x_1268_);
v___x_1270_ = v___x_1250_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___f_1260_);
v___x_1270_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_13324__overap_1273_; lean_object* v___x_1274_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = l_instInhabitedOfMonad___redArg(v___x_1270_, v___x_1271_);
v___x_13324__overap_1273_ = lean_panic_fn_borrowed(v___x_1272_, v_msg_1216_);
lean_dec(v___x_1272_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___x_1274_ = lean_apply_5(v___x_13324__overap_1273_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, lean_box(0));
return v___x_1274_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v_msg_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1300_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4));
v___x_1301_ = lean_unsigned_to_nat(11u);
v___x_1302_ = lean_unsigned_to_nat(122u);
v___x_1303_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3));
v___x_1304_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2));
v___x_1305_ = l_mkPanicMessageWithDecl(v___x_1304_, v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(lean_object* v_constName_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1320_; lean_object* v_env_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1320_ = lean_st_ref_get(v___y_1310_);
v_env_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_ref(v_env_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = 0;
lean_inc(v_constName_1306_);
v___x_1323_ = l_Lean_Environment_findAsync_x3f(v_env_1321_, v_constName_1306_, v___x_1322_);
if (lean_obj_tag(v___x_1323_) == 1)
{
lean_object* v_val_1324_; uint8_t v_kind_1325_; 
v_val_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v_kind_1325_ = lean_ctor_get_uint8(v_val_1324_, sizeof(void*)*3);
if (v_kind_1325_ == 6)
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1324_);
if (lean_obj_tag(v___x_1326_) == 6)
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_constName_1306_);
v_val_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 0);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_val_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref(v___x_1326_);
v___x_1335_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_1336_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_1335_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1345_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1345_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
if (lean_obj_tag(v_a_1337_) == 0)
{
lean_del_object(v___x_1339_);
goto v___jp_1312_;
}
else
{
lean_object* v_val_1341_; lean_object* v___x_1343_; 
lean_dec(v_constName_1306_);
v_val_1341_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v_a_1337_, 1);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_val_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_val_1341_);
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
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_constName_1306_);
v_a_1346_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1336_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_dec(v_val_1324_);
goto v___jp_1312_;
}
}
else
{
lean_dec(v___x_1323_);
goto v___jp_1312_;
}
v___jp_1312_:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1313_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1314_ = 0;
v___x_1315_ = l_Lean_MessageData_ofConstName(v_constName_1306_, v___x_1314_);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1313_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1316_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1318_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(lean_object* v_constName_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v_constName_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1360_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0));
v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_env_1371_; lean_object* v___x_1372_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_env_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc_ref(v_env_1371_);
lean_dec(v___x_1370_);
lean_inc(v_constName_1364_);
v___x_1372_ = l_Lean_isInductiveCore_x3f(v_env_1371_, v_constName_1364_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1373_ = lean_obj_once(&l_Lean_Meta_getStructureName___closed__1, &l_Lean_Meta_getStructureName___closed__1_once, _init_l_Lean_Meta_getStructureName___closed__1);
v___x_1374_ = 0;
v___x_1375_ = l_Lean_MessageData_ofConstName(v_constName_1364_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1378_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v_constName_1364_);
v_val_1380_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1372_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v___x_1372_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_val_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(lean_object* v_constName_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_constName_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1394_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__0));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_Meta_mkProjections___lam__2___closed__2));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2(lean_object* v_n_1401_, lean_object* v___x_1402_, uint8_t v_instImplicit_1403_, lean_object* v_projDecls_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
lean_inc(v_n_1401_);
v___x_1410_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(v_n_1401_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1452_ = l_Lean_InductiveVal_numCtors(v_a_1411_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_dec_eq(v___x_1452_, v___x_1453_);
lean_dec(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
lean_dec(v_a_1411_);
lean_dec_ref(v_projDecls_1404_);
v___x_1455_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__1, &l_Lean_Meta_mkProjections___lam__2___closed__1_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__1);
v___x_1456_ = l_Lean_MessageData_ofConstName(v_n_1401_, v___x_1454_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lean_Meta_mkProjections___lam__2___closed__3, &l_Lean_Meta_mkProjections___lam__2___closed__3_once, _init_l_Lean_Meta_mkProjections___lam__2___closed__3);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(v___x_1459_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1460_;
}
else
{
v___y_1413_ = v___y_1405_;
v___y_1414_ = v___y_1406_;
v___y_1415_ = v___y_1407_;
v___y_1416_ = v___y_1408_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v_toConstantVal_1417_; lean_object* v_numParams_1418_; lean_object* v_ctors_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_toConstantVal_1417_ = lean_ctor_get(v_a_1411_, 0);
lean_inc_ref(v_toConstantVal_1417_);
v_numParams_1418_ = lean_ctor_get(v_a_1411_, 1);
lean_inc(v_numParams_1418_);
v_ctors_1419_ = lean_ctor_get(v_a_1411_, 4);
lean_inc(v_ctors_1419_);
lean_dec(v_a_1411_);
v___x_1420_ = l_List_head_x21___redArg(v___x_1402_, v_ctors_1419_);
lean_dec(v_ctors_1419_);
v___x_1421_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(v___x_1420_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_levelParams_1423_; lean_object* v_type_1424_; lean_object* v___x_1425_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_levelParams_1423_ = lean_ctor_get(v_toConstantVal_1417_, 1);
lean_inc(v_levelParams_1423_);
v_type_1424_ = lean_ctor_get(v_toConstantVal_1417_, 2);
lean_inc_ref(v_type_1424_);
lean_dec_ref(v_toConstantVal_1417_);
v___x_1425_ = l_Lean_Meta_isPropFormerType(v_type_1424_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_toConstantVal_1426_; lean_object* v_a_1427_; lean_object* v_type_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v_toConstantVal_1426_ = lean_ctor_get(v_a_1422_, 0);
lean_inc_ref(v_toConstantVal_1426_);
lean_dec(v_a_1422_);
v_a_1427_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1425_, 1);
v_type_1428_ = lean_ctor_get(v_toConstantVal_1426_, 2);
lean_inc_ref(v_type_1428_);
v___x_1429_ = lean_box(0);
lean_inc(v_levelParams_1423_);
v___x_1430_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(v_levelParams_1423_, v___x_1429_);
v___x_1431_ = lean_box(v_instImplicit_1403_);
lean_inc(v_numParams_1418_);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__1___boxed), 15, 8);
lean_closure_set(v___f_1432_, 0, v___x_1431_);
lean_closure_set(v___f_1432_, 1, v_projDecls_1404_);
lean_closure_set(v___f_1432_, 2, v_toConstantVal_1426_);
lean_closure_set(v___f_1432_, 3, v_numParams_1418_);
lean_closure_set(v___f_1432_, 4, v___x_1430_);
lean_closure_set(v___f_1432_, 5, v_n_1401_);
lean_closure_set(v___f_1432_, 6, v_levelParams_1423_);
lean_closure_set(v___f_1432_, 7, v_a_1427_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_numParams_1418_);
v___x_1434_ = 0;
v___x_1435_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__11___redArg(v_type_1428_, v___x_1433_, v___f_1432_, v___x_1434_, v___x_1434_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_levelParams_1423_);
lean_dec(v_a_1422_);
lean_dec(v_numParams_1418_);
lean_dec_ref(v_projDecls_1404_);
lean_dec(v_n_1401_);
v_a_1436_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1425_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1425_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_numParams_1418_);
lean_dec_ref(v_toConstantVal_1417_);
lean_dec_ref(v_projDecls_1404_);
lean_dec(v_n_1401_);
v_a_1444_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1421_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1421_);
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
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_projDecls_1404_);
lean_dec(v_n_1401_);
v_a_1461_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1410_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1410_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___lam__2___boxed(lean_object* v_n_1469_, lean_object* v___x_1470_, lean_object* v_instImplicit_1471_, lean_object* v_projDecls_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v_instImplicit_boxed_1478_; lean_object* v_res_1479_; 
v_instImplicit_boxed_1478_ = lean_unbox(v_instImplicit_1471_);
v_res_1479_ = l_Lean_Meta_mkProjections___lam__2(v_n_1469_, v___x_1470_, v_instImplicit_boxed_1478_, v_projDecls_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___x_1470_);
return v_res_1479_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__0(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5___redArg___closed__0);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(32u);
v___x_1483_ = lean_mk_empty_array_with_capacity(v___x_1482_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__2(void){
_start:
{
size_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = ((size_t)5ULL);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_unsigned_to_nat(32u);
v___x_1488_ = lean_mk_empty_array_with_capacity(v___x_1487_);
v___x_1489_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__1, &l_Lean_Meta_mkProjections___closed__1_once, _init_l_Lean_Meta_mkProjections___closed__1);
v___x_1490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
lean_ctor_set(v___x_1490_, 1, v___x_1488_);
lean_ctor_set(v___x_1490_, 2, v___x_1486_);
lean_ctor_set(v___x_1490_, 3, v___x_1486_);
lean_ctor_set_usize(v___x_1490_, 4, v___x_1485_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjections___closed__3(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = lean_box(1);
v___x_1492_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__2, &l_Lean_Meta_mkProjections___closed__2_once, _init_l_Lean_Meta_mkProjections___closed__2);
v___x_1493_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__0, &l_Lean_Meta_mkProjections___closed__0_once, _init_l_Lean_Meta_mkProjections___closed__0);
v___x_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1492_);
lean_ctor_set(v___x_1494_, 2, v___x_1491_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections(lean_object* v_n_1497_, lean_object* v_projDecls_1498_, uint8_t v_instImplicit_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___f_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_box(v_instImplicit_1499_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Meta_mkProjections___lam__2___boxed), 9, 4);
lean_closure_set(v___f_1507_, 0, v_n_1497_);
lean_closure_set(v___f_1507_, 1, v___x_1505_);
lean_closure_set(v___f_1507_, 2, v___x_1506_);
lean_closure_set(v___f_1507_, 3, v_projDecls_1498_);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_mkProjections___closed__3, &l_Lean_Meta_mkProjections___closed__3_once, _init_l_Lean_Meta_mkProjections___closed__3);
v___x_1509_ = ((lean_object*)(l_Lean_Meta_mkProjections___closed__4));
v___x_1510_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__12___redArg(v___x_1508_, v___x_1509_, v___f_1507_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjections___boxed(lean_object* v_n_1511_, lean_object* v_projDecls_1512_, lean_object* v_instImplicit_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
uint8_t v_instImplicit_boxed_1519_; lean_object* v_res_1520_; 
v_instImplicit_boxed_1519_ = lean_unbox(v_instImplicit_1513_);
v_res_1520_ = l_Lean_Meta_mkProjections(v_n_1511_, v_projDecls_1512_, v_instImplicit_boxed_1519_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(uint8_t v_instImplicit_1521_, lean_object* v_as_1522_, size_t v_sz_1523_, size_t v_i_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_1521_, v_as_1522_, v_sz_1523_, v_i_1524_, v_b_1525_, v___y_1526_, v___y_1528_, v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(lean_object* v_instImplicit_1532_, lean_object* v_as_1533_, lean_object* v_sz_1534_, lean_object* v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_instImplicit_boxed_1542_; size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_instImplicit_boxed_1542_ = lean_unbox(v_instImplicit_1532_);
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1534_);
lean_dec(v_sz_1534_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1535_);
lean_dec(v_i_1535_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_1542_, v_as_1533_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_as_1533_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4_spec__5(lean_object* v_00_u03b2_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg(){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(lean_object* v___dummy_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4___redArg();
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Meta_mkProjections_spec__4(lean_object* v_00_u03b2_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg___closed__2);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7(lean_object* v_00_u03b1_1554_, lean_object* v_ref_1555_, lean_object* v_msg_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___redArg(v_ref_1555_, v_msg_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_ref_1564_, lean_object* v_msg_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__7(v_00_u03b1_1563_, v_ref_1564_, v_msg_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v_ref_1564_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8(lean_object* v_00_u03b1_1572_, lean_object* v_x_1573_, uint8_t v_when_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___redArg(v_x_1573_, v_when_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_x_1582_, lean_object* v_when_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v_when_boxed_1589_; lean_object* v_res_1590_; 
v_when_boxed_1589_ = lean_unbox(v_when_1583_);
v_res_1590_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8(v_00_u03b1_1581_, v_x_1582_, v_when_boxed_1589_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(lean_object* v_upperBound_1591_, lean_object* v_projDecls_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, uint8_t v_instImplicit_1595_, lean_object* v___x_1596_, lean_object* v_params_1597_, lean_object* v_self_1598_, lean_object* v_a_1599_, lean_object* v___x_1600_, lean_object* v_n_1601_, lean_object* v___x_1602_, uint8_t v_a_1603_, lean_object* v_inst_1604_, lean_object* v_R_1605_, lean_object* v_a_1606_, lean_object* v_b_1607_, lean_object* v_c_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___redArg(v_upperBound_1591_, v_projDecls_1592_, v___x_1593_, v___x_1594_, v_instImplicit_1595_, v___x_1596_, v_params_1597_, v_self_1598_, v_a_1599_, v___x_1600_, v_n_1601_, v___x_1602_, v_a_1603_, v_a_1606_, v_b_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9___boxed(lean_object** _args){
lean_object* v_upperBound_1615_ = _args[0];
lean_object* v_projDecls_1616_ = _args[1];
lean_object* v___x_1617_ = _args[2];
lean_object* v___x_1618_ = _args[3];
lean_object* v_instImplicit_1619_ = _args[4];
lean_object* v___x_1620_ = _args[5];
lean_object* v_params_1621_ = _args[6];
lean_object* v_self_1622_ = _args[7];
lean_object* v_a_1623_ = _args[8];
lean_object* v___x_1624_ = _args[9];
lean_object* v_n_1625_ = _args[10];
lean_object* v___x_1626_ = _args[11];
lean_object* v_a_1627_ = _args[12];
lean_object* v_inst_1628_ = _args[13];
lean_object* v_R_1629_ = _args[14];
lean_object* v_a_1630_ = _args[15];
lean_object* v_b_1631_ = _args[16];
lean_object* v_c_1632_ = _args[17];
lean_object* v___y_1633_ = _args[18];
lean_object* v___y_1634_ = _args[19];
lean_object* v___y_1635_ = _args[20];
lean_object* v___y_1636_ = _args[21];
lean_object* v___y_1637_ = _args[22];
_start:
{
uint8_t v_instImplicit_boxed_1638_; uint8_t v_a_19294__boxed_1639_; lean_object* v_res_1640_; 
v_instImplicit_boxed_1638_ = lean_unbox(v_instImplicit_1619_);
v_a_19294__boxed_1639_ = lean_unbox(v_a_1627_);
v_res_1640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__9(v_upperBound_1615_, v_projDecls_1616_, v___x_1617_, v___x_1618_, v_instImplicit_boxed_1638_, v___x_1620_, v_params_1621_, v_self_1622_, v_a_1623_, v___x_1624_, v_n_1625_, v___x_1626_, v_a_19294__boxed_1639_, v_inst_1628_, v_R_1629_, v_a_1630_, v_b_1631_, v_c_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v_projDecls_1616_);
lean_dec(v_upperBound_1615_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8(lean_object* v_declName_1641_, uint8_t v_s_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___redArg(v_declName_1641_, v_s_1642_, v___y_1644_, v___y_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8___boxed(lean_object* v_declName_1649_, lean_object* v_s_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v_s_boxed_1656_; lean_object* v_res_1657_; 
v_s_boxed_1656_ = lean_unbox(v_s_1650_);
v_res_1657_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__6_spec__8(v_declName_1649_, v_s_boxed_1656_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11(lean_object* v_00_u03b1_1658_, lean_object* v_x_1659_, uint8_t v_isExporting_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___redArg(v_x_1659_, v_isExporting_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_x_1668_, lean_object* v_isExporting_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v_isExporting_boxed_1675_; lean_object* v_res_1676_; 
v_isExporting_boxed_1675_ = lean_unbox(v_isExporting_1669_);
v_res_1676_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__8_spec__11(v_00_u03b1_1667_, v_x_1668_, v_isExporting_boxed_1675_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(lean_object* v_k_1677_, uint8_t v_allowLevelAssignments_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1678_, v_k_1677_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1684_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1684_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(lean_object* v_k_1701_, lean_object* v_allowLevelAssignments_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1708_; lean_object* v_res_1709_; 
v_allowLevelAssignments_boxed_1708_ = lean_unbox(v_allowLevelAssignments_1702_);
v_res_1709_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1701_, v_allowLevelAssignments_boxed_1708_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(lean_object* v_00_u03b1_1710_, lean_object* v_k_1711_, uint8_t v_allowLevelAssignments_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_1711_, v_allowLevelAssignments_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_k_1720_, lean_object* v_allowLevelAssignments_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1727_; lean_object* v_res_1728_; 
v_allowLevelAssignments_boxed_1727_ = lean_unbox(v_allowLevelAssignments_1721_);
v_res_1728_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_1719_, v_k_1720_, v_allowLevelAssignments_boxed_1727_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(lean_object* v_as_1729_, size_t v_sz_1730_, size_t v_i_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_lt(v_i_1731_, v_sz_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1732_);
return v___x_1739_;
}
else
{
lean_object* v_snd_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1795_; 
v_snd_1740_ = lean_ctor_get(v_b_1732_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_b_1732_, 0);
lean_dec(v_unused_1796_);
v___x_1742_ = v_b_1732_;
v_isShared_1743_ = v_isSharedCheck_1795_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_snd_1740_);
lean_dec(v_b_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1795_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_array_1744_; lean_object* v_start_1745_; lean_object* v_stop_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_array_1744_ = lean_ctor_get(v_snd_1740_, 0);
v_start_1745_ = lean_ctor_get(v_snd_1740_, 1);
v_stop_1746_ = lean_ctor_get(v_snd_1740_, 2);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_nat_dec_lt(v_start_1745_, v_stop_1746_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1750_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1747_);
v___x_1750_ = v___x_1742_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_snd_1740_);
v___x_1750_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
else
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1791_; 
lean_inc(v_stop_1746_);
lean_inc(v_start_1745_);
lean_inc_ref(v_array_1744_);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_snd_1740_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; lean_object* v_unused_1793_; lean_object* v_unused_1794_; 
v_unused_1792_ = lean_ctor_get(v_snd_1740_, 2);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_snd_1740_, 1);
lean_dec(v_unused_1793_);
v_unused_1794_ = lean_ctor_get(v_snd_1740_, 0);
lean_dec(v_unused_1794_);
v___x_1754_ = v_snd_1740_;
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v_snd_1740_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_a_1756_ = lean_array_uget_borrowed(v_as_1729_, v_i_1731_);
v___x_1757_ = lean_array_fget(v_array_1744_, v_start_1745_);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_start_1745_, v___x_1758_);
lean_dec(v_start_1745_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1759_);
v___x_1761_ = v___x_1754_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_array_1744_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_stop_1746_);
v___x_1761_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; 
lean_inc(v_a_1756_);
v___x_1762_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1756_, v___x_1757_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1781_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1781_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1781_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_unbox(v_a_1763_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_a_1763_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1761_);
lean_ctor_set(v___x_1742_, 0, v___x_1768_);
v___x_1770_ = v___x_1742_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1761_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1770_);
v___x_1772_ = v___x_1765_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
lean_object* v___x_1776_; 
lean_del_object(v___x_1765_);
lean_dec(v_a_1763_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1761_);
lean_ctor_set(v___x_1742_, 0, v___x_1747_);
v___x_1776_ = v___x_1742_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1761_);
v___x_1776_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
size_t v___x_1777_; size_t v___x_1778_; 
v___x_1777_ = ((size_t)1ULL);
v___x_1778_ = lean_usize_add(v_i_1731_, v___x_1777_);
v_i_1731_ = v___x_1778_;
v_b_1732_ = v___x_1776_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___x_1761_);
lean_del_object(v___x_1742_);
v_a_1782_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1762_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1762_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(lean_object* v_as_1797_, lean_object* v_sz_1798_, lean_object* v_i_1799_, lean_object* v_b_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
size_t v_sz_boxed_1806_; size_t v_i_boxed_1807_; lean_object* v_res_1808_; 
v_sz_boxed_1806_ = lean_unbox_usize(v_sz_1798_);
lean_dec(v_sz_1798_);
v_i_boxed_1807_ = lean_unbox_usize(v_i_1799_);
lean_dec(v_i_1799_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_1797_, v_sz_boxed_1806_, v_i_boxed_1807_, v_b_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_as_1797_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(uint8_t v___x_1809_, lean_object* v_params2_1810_, lean_object* v___x_1811_, lean_object* v_params1_1812_, uint8_t v___x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
if (v___x_1809_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v___x_1811_);
lean_dec_ref(v_params2_1810_);
v___x_1819_ = lean_box(v___x_1809_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = l_Array_toSubarray___redArg(v_params2_1810_, v___x_1821_, v___x_1811_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
v_sz_1825_ = lean_array_size(v_params1_1812_);
v___x_1826_ = ((size_t)0ULL);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_1812_, v_sz_1825_, v___x_1826_, v___x_1824_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1841_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1841_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_fst_1832_; 
v_fst_1832_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_fst_1832_);
lean_dec(v_a_1828_);
if (lean_obj_tag(v_fst_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_box(v___x_1813_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1833_);
v___x_1835_ = v___x_1830_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_val_1837_; lean_object* v___x_1839_; 
v_val_1837_ = lean_ctor_get(v_fst_1832_, 0);
lean_inc(v_val_1837_);
lean_dec_ref_known(v_fst_1832_, 1);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v_val_1837_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_val_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1827_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1827_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(lean_object* v___x_1850_, lean_object* v_params2_1851_, lean_object* v___x_1852_, lean_object* v_params1_1853_, lean_object* v___x_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
uint8_t v___x_2007__boxed_1860_; uint8_t v___x_2009__boxed_1861_; lean_object* v_res_1862_; 
v___x_2007__boxed_1860_ = lean_unbox(v___x_1850_);
v___x_2009__boxed_1861_ = lean_unbox(v___x_1854_);
v_res_1862_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(v___x_2007__boxed_1860_, v_params2_1851_, v___x_1852_, v_params1_1853_, v___x_2009__boxed_1861_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec_ref(v_params1_1853_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(lean_object* v_params1_1863_, lean_object* v_params2_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___y_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; 
v___x_1870_ = lean_array_get_size(v_params1_1863_);
v___x_1871_ = lean_array_get_size(v_params2_1864_);
v___x_1872_ = lean_nat_dec_eq(v___x_1870_, v___x_1871_);
v___x_1873_ = 1;
v___x_1874_ = lean_box(v___x_1872_);
v___x_1875_ = lean_box(v___x_1873_);
v___y_1876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed), 10, 5);
lean_closure_set(v___y_1876_, 0, v___x_1874_);
lean_closure_set(v___y_1876_, 1, v_params2_1864_);
lean_closure_set(v___y_1876_, 2, v___x_1871_);
lean_closure_set(v___y_1876_, 3, v_params1_1863_);
lean_closure_set(v___y_1876_, 4, v___x_1875_);
v___x_1877_ = 0;
v___x_1878_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_1876_, v___x_1877_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(lean_object* v_params1_1879_, lean_object* v_params2_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params1_1879_, v_params2_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(lean_object* v_declName_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = lean_st_ref_get(v___y_1888_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1891_, v_declName_1887_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(lean_object* v_declName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1894_, v___y_1895_);
lean_dec(v___y_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(lean_object* v_declName_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1898_, v___y_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0(void){
_start:
{
lean_object* v___x_1912_; lean_object* v_dummy_1913_; 
v___x_1912_ = lean_box(0);
v_dummy_1913_ = l_Lean_Expr_sort___override(v___x_1912_);
return v_dummy_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(lean_object* v_ctor_1914_, lean_object* v_induct_1915_, lean_object* v_params_1916_, lean_object* v_idx_1917_, lean_object* v_e_1918_, lean_object* v_x_x3f_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
if (lean_obj_tag(v_e_1918_) == 11)
{
lean_object* v_typeName_1931_; lean_object* v_idx_1932_; lean_object* v_struct_1933_; uint8_t v___x_1980_; 
v_typeName_1931_ = lean_ctor_get(v_e_1918_, 0);
v_idx_1932_ = lean_ctor_get(v_e_1918_, 1);
v_struct_1933_ = lean_ctor_get(v_e_1918_, 2);
lean_inc_ref(v_struct_1933_);
v___x_1980_ = lean_nat_dec_eq(v_idx_1932_, v_idx_1917_);
if (v___x_1980_ == 0)
{
lean_dec_ref(v_struct_1933_);
lean_dec_ref_known(v_e_1918_, 3);
lean_dec_ref(v_params_1916_);
goto v___jp_1928_;
}
else
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_name_eq(v_induct_1915_, v_typeName_1931_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v_struct_1933_);
lean_dec_ref_known(v_e_1918_, 3);
lean_dec_ref(v_params_1916_);
goto v___jp_1928_;
}
else
{
if (lean_obj_tag(v_x_x3f_1919_) == 0)
{
goto v___jp_1934_;
}
else
{
lean_object* v_val_1982_; uint8_t v___x_1983_; 
v_val_1982_ = lean_ctor_get(v_x_x3f_1919_, 0);
v___x_1983_ = lean_expr_eqv(v_val_1982_, v_struct_1933_);
if (v___x_1983_ == 0)
{
lean_dec_ref(v_struct_1933_);
lean_dec_ref_known(v_e_1918_, 3);
lean_dec_ref(v_params_1916_);
goto v___jp_1928_;
}
else
{
goto v___jp_1934_;
}
}
}
}
v___jp_1934_:
{
lean_object* v___x_1935_; 
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
v___x_1935_ = lean_infer_type(v_e_1918_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_a_1921_);
lean_inc_ref(v_a_1920_);
v___x_1937_ = lean_whnf(v_a_1936_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_dummy_1939_; lean_object* v_nargs_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_dummy_1939_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_1940_ = l_Lean_Expr_getAppNumArgs(v_a_1938_);
lean_inc(v_nargs_1940_);
v___x_1941_ = lean_mk_array(v_nargs_1940_, v_dummy_1939_);
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_nat_sub(v_nargs_1940_, v___x_1942_);
lean_dec(v_nargs_1940_);
v___x_1944_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1938_, v___x_1941_, v___x_1943_);
v___x_1945_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1916_, v___x_1944_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1955_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1955_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
if (v___x_1950_ == 0)
{
lean_del_object(v___x_1948_);
lean_dec_ref(v_struct_1933_);
goto v___jp_1928_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_struct_1933_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1951_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
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
lean_dec_ref(v_struct_1933_);
v_a_1956_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1945_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1945_);
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
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_struct_1933_);
lean_dec_ref(v_params_1916_);
v_a_1964_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1937_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1937_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_struct_1933_);
lean_dec_ref(v_params_1916_);
v_a_1972_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1935_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1935_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Expr_getAppFn(v_e_1918_);
if (lean_obj_tag(v___x_1984_) == 4)
{
lean_object* v_declName_1985_; lean_object* v___x_1986_; lean_object* v_a_1987_; 
v_declName_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_declName_1985_);
lean_dec_ref_known(v___x_1984_, 2);
v___x_1986_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_1985_, v_a_1923_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
if (lean_obj_tag(v_a_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2032_; 
v_val_1988_ = lean_ctor_get(v_a_1987_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_1987_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1990_ = v_a_1987_;
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_val_1988_);
lean_dec(v_a_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2032_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_ctorName_1992_; lean_object* v_numParams_1993_; lean_object* v_i_1994_; uint8_t v___x_1995_; 
v_ctorName_1992_ = lean_ctor_get(v_val_1988_, 0);
lean_inc(v_ctorName_1992_);
v_numParams_1993_ = lean_ctor_get(v_val_1988_, 1);
lean_inc(v_numParams_1993_);
v_i_1994_ = lean_ctor_get(v_val_1988_, 2);
lean_inc(v_i_1994_);
lean_dec(v_val_1988_);
v___x_1995_ = lean_name_eq(v_ctorName_1992_, v_ctor_1914_);
lean_dec(v_ctorName_1992_);
if (v___x_1995_ == 0)
{
lean_dec(v_i_1994_);
lean_dec(v_numParams_1993_);
lean_del_object(v___x_1990_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_eq(v_i_1994_, v_idx_1917_);
lean_dec(v_i_1994_);
if (v___x_1996_ == 0)
{
lean_dec(v_numParams_1993_);
lean_del_object(v___x_1990_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1997_ = l_Lean_Expr_getAppNumArgs(v_e_1918_);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_add(v_numParams_1993_, v___x_1998_);
lean_dec(v_numParams_1993_);
v___x_2000_ = lean_nat_dec_eq(v___x_1997_, v___x_1999_);
lean_dec(v___x_1999_);
lean_dec(v___x_1997_);
if (v___x_2000_ == 0)
{
lean_del_object(v___x_1990_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Expr_appArg_x21(v_e_1918_);
if (lean_obj_tag(v_x_x3f_1919_) == 0)
{
goto v___jp_2002_;
}
else
{
lean_object* v_val_2030_; uint8_t v___x_2031_; 
v_val_2030_ = lean_ctor_get(v_x_x3f_1919_, 0);
v___x_2031_ = lean_expr_eqv(v_val_2030_, v___x_2001_);
if (v___x_2031_ == 0)
{
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1990_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
else
{
goto v___jp_2002_;
}
}
v___jp_2002_:
{
lean_object* v___x_2003_; lean_object* v_dummy_2004_; lean_object* v_nargs_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2003_ = l_Lean_Expr_appFn_x21(v_e_1918_);
lean_dec_ref(v_e_1918_);
v_dummy_2004_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
v_nargs_2005_ = l_Lean_Expr_getAppNumArgs(v___x_2003_);
lean_inc(v_nargs_2005_);
v___x_2006_ = lean_mk_array(v_nargs_2005_, v_dummy_2004_);
v___x_2007_ = lean_nat_sub(v_nargs_2005_, v___x_1998_);
lean_dec(v_nargs_2005_);
v___x_2008_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2003_, v___x_2006_, v___x_2007_);
v___x_2009_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(v_params_1916_, v___x_2008_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2021_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2021_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2014_ == 0)
{
lean_del_object(v___x_2012_);
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1990_);
goto v___jp_1925_;
}
else
{
lean_object* v___x_2016_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2001_);
v___x_2016_ = v___x_1990_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2001_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2016_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v___x_2001_);
lean_del_object(v___x_1990_);
v_a_2022_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2009_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2009_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
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
lean_dec(v_a_1987_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
}
else
{
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_e_1918_);
lean_dec_ref(v_params_1916_);
goto v___jp_1925_;
}
}
v___jp_1925_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
v___jp_1928_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(lean_object* v_ctor_2033_, lean_object* v_induct_2034_, lean_object* v_params_2035_, lean_object* v_idx_2036_, lean_object* v_e_2037_, lean_object* v_x_x3f_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_ctor_2033_, v_induct_2034_, v_params_2035_, v_idx_2036_, v_e_2037_, v_x_x3f_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_x_x3f_2038_);
lean_dec(v_idx_2036_);
lean_dec(v_induct_2034_);
lean_dec(v_ctor_2033_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(lean_object* v_constName_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v_env_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2051_ = lean_st_ref_get(v___y_2049_);
v_env_2055_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2055_);
lean_dec(v___x_2051_);
v___x_2056_ = 0;
v___x_2057_ = l_Lean_Environment_findAsync_x3f(v_env_2055_, v_constName_2045_, v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 1)
{
lean_object* v_val_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2077_; 
v_val_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_val_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint8_t v_kind_2062_; 
v_kind_2062_ = lean_ctor_get_uint8(v_val_2058_, sizeof(void*)*3);
if (v_kind_2062_ == 6)
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2058_);
if (lean_obj_tag(v___x_2063_) == 6)
{
lean_object* v_val_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2074_; 
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2074_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_val_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2074_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v_val_2064_);
v___x_2069_ = v___x_2060_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_val_2064_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec_ref(v___x_2063_);
lean_del_object(v___x_2060_);
v___x_2075_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
v___x_2076_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_2075_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2076_;
}
}
else
{
lean_del_object(v___x_2060_);
lean_dec(v_val_2058_);
goto v___jp_2052_;
}
}
}
else
{
lean_dec(v___x_2057_);
goto v___jp_2052_;
}
v___jp_2052_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(lean_object* v_constName_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_constName_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(lean_object* v_upperBound_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v_declName_2096_, lean_object* v___x_2097_, lean_object* v___x_2098_, lean_object* v_a_2099_, lean_object* v_val_2100_, lean_object* v_a_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_lt(v_a_2101_, v_upperBound_2093_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec(v_a_2101_);
lean_dec_ref(v___x_2098_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_b_2102_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec_ref(v_b_2102_);
v___x_2110_ = l_Lean_instInhabitedExpr;
v___x_2111_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2112_ = lean_nat_add(v___x_2094_, v_a_2101_);
v___x_2113_ = lean_array_get_borrowed(v___x_2110_, v___x_2095_, v___x_2112_);
lean_dec(v___x_2112_);
lean_inc(v___x_2113_);
lean_inc_ref(v___x_2098_);
v___x_2114_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2096_, v___x_2097_, v___x_2098_, v_a_2101_, v___x_2113_, v_a_2099_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2132_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2132_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2132_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
if (lean_obj_tag(v_a_2115_) == 1)
{
lean_object* v_val_2119_; uint8_t v___x_2120_; 
v_val_2119_ = lean_ctor_get(v_a_2115_, 0);
lean_inc(v_val_2119_);
lean_dec_ref_known(v_a_2115_, 1);
v___x_2120_ = lean_expr_eqv(v_val_2119_, v_val_2100_);
lean_dec(v_val_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_a_2101_);
lean_dec_ref(v___x_2098_);
v___x_2121_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2121_);
v___x_2123_ = v___x_2117_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_del_object(v___x_2117_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v_a_2101_, v___x_2125_);
lean_dec(v_a_2101_);
v_a_2101_ = v___x_2126_;
v_b_2102_ = v___x_2111_;
goto _start;
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec(v_a_2115_);
lean_dec(v_a_2101_);
lean_dec_ref(v___x_2098_);
v___x_2128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2));
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2128_);
v___x_2130_ = v___x_2117_;
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
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2101_);
lean_dec_ref(v___x_2098_);
v_a_2133_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2114_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2114_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_declName_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_a_2147_, lean_object* v_val_2148_, lean_object* v_a_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2141_, v___x_2142_, v___x_2143_, v_declName_2144_, v___x_2145_, v___x_2146_, v_a_2147_, v_val_2148_, v_a_2149_, v_b_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec_ref(v_val_2148_);
lean_dec(v_a_2147_);
lean_dec(v___x_2145_);
lean_dec(v_declName_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
lean_dec(v_upperBound_2141_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f(lean_object* v_e_2157_, lean_object* v_p_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Expr_getAppFn(v_e_2157_);
if (lean_obj_tag(v___x_2164_) == 4)
{
lean_object* v_declName_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_declName_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_n(v_declName_2165_, 2);
lean_dec_ref_known(v___x_2164_, 2);
v___x_2166_ = l_Lean_instInhabitedExpr;
v___x_2167_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(v_declName_2165_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2239_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2239_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2239_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2236_; 
v_val_2177_ = lean_ctor_get(v_a_2168_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2168_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2179_ = v_a_2168_;
v_isShared_2180_ = v_isSharedCheck_2236_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_val_2177_);
lean_dec(v_a_2168_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2236_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_induct_2181_; lean_object* v_numParams_2182_; lean_object* v_numFields_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_induct_2181_ = lean_ctor_get(v_val_2177_, 1);
lean_inc_n(v_induct_2181_, 2);
v_numParams_2182_ = lean_ctor_get(v_val_2177_, 3);
lean_inc(v_numParams_2182_);
v_numFields_2183_ = lean_ctor_get(v_val_2177_, 4);
lean_inc(v_numFields_2183_);
lean_dec(v_val_2177_);
v___x_2184_ = lean_apply_1(v_p_2158_, v_induct_2181_);
v___x_2185_ = lean_unbox(v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_dec(v_numFields_2183_);
lean_dec(v_numParams_2182_);
lean_dec(v_induct_2181_);
lean_del_object(v___x_2170_);
lean_dec(v_declName_2165_);
lean_dec_ref(v_e_2157_);
v___x_2186_ = lean_box(0);
if (v_isShared_2180_ == 0)
{
lean_ctor_set_tag(v___x_2179_, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2186_);
v___x_2188_ = v___x_2179_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
lean_del_object(v___x_2179_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_nat_dec_lt(v___x_2190_, v_numFields_2183_);
if (v___x_2191_ == 0)
{
lean_dec(v_numFields_2183_);
lean_dec(v_numParams_2182_);
lean_dec(v_induct_2181_);
lean_dec(v_declName_2165_);
lean_dec_ref(v_e_2157_);
goto v___jp_2172_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = l_Lean_Expr_getAppNumArgs(v_e_2157_);
v___x_2193_ = lean_nat_add(v_numParams_2182_, v_numFields_2183_);
v___x_2194_ = lean_nat_dec_eq(v___x_2192_, v___x_2193_);
lean_dec(v___x_2193_);
if (v___x_2194_ == 0)
{
lean_dec(v___x_2192_);
lean_dec(v_numFields_2183_);
lean_dec(v_numParams_2182_);
lean_dec(v_induct_2181_);
lean_dec(v_declName_2165_);
lean_dec_ref(v_e_2157_);
goto v___jp_2172_;
}
else
{
lean_object* v_dummy_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_del_object(v___x_2170_);
v_dummy_2195_ = lean_obj_once(&l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0, &l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once, _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
lean_inc(v___x_2192_);
v___x_2196_ = lean_mk_array(v___x_2192_, v_dummy_2195_);
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_sub(v___x_2192_, v___x_2197_);
lean_dec(v___x_2192_);
v___x_2199_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2157_, v___x_2196_, v___x_2198_);
lean_inc(v_numParams_2182_);
v___x_2200_ = l_Array_extract___redArg(v___x_2199_, v___x_2190_, v_numParams_2182_);
v___x_2201_ = lean_array_get_borrowed(v___x_2166_, v___x_2199_, v_numParams_2182_);
v___x_2202_ = lean_box(0);
lean_inc(v___x_2201_);
lean_inc_ref(v___x_2200_);
v___x_2203_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(v_declName_2165_, v_induct_2181_, v___x_2200_, v___x_2190_, v___x_2201_, v___x_2202_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2235_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2235_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2235_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
if (lean_obj_tag(v_a_2204_) == 1)
{
lean_object* v_val_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_del_object(v___x_2206_);
v_val_2208_ = lean_ctor_get(v_a_2204_, 0);
v___x_2209_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0));
v___x_2210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_2183_, v_numParams_2182_, v___x_2199_, v_declName_2165_, v_induct_2181_, v___x_2200_, v_a_2204_, v_val_2208_, v___x_2197_, v___x_2209_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_induct_2181_);
lean_dec(v_declName_2165_);
lean_dec_ref(v___x_2199_);
lean_dec(v_numParams_2182_);
lean_dec(v_numFields_2183_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2223_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_fst_2215_; 
v_fst_2215_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_fst_2215_);
lean_dec(v_a_2211_);
if (lean_obj_tag(v_fst_2215_) == 0)
{
lean_object* v___x_2217_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_a_2204_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2204_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v_val_2219_; lean_object* v___x_2221_; 
lean_dec_ref_known(v_a_2204_, 1);
v_val_2219_ = lean_ctor_get(v_fst_2215_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v_fst_2215_, 1);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_val_2219_);
v___x_2221_ = v___x_2213_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_val_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec_ref_known(v_a_2204_, 1);
v_a_2224_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2210_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2210_);
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
lean_object* v___x_2233_; 
lean_dec(v_a_2204_);
lean_dec_ref(v___x_2200_);
lean_dec_ref(v___x_2199_);
lean_dec(v_numFields_2183_);
lean_dec(v_numParams_2182_);
lean_dec(v_induct_2181_);
lean_dec(v_declName_2165_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2202_);
v___x_2233_ = v___x_2206_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2202_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_dec_ref(v___x_2200_);
lean_dec_ref(v___x_2199_);
lean_dec(v_numFields_2183_);
lean_dec(v_numParams_2182_);
lean_dec(v_induct_2181_);
lean_dec(v_declName_2165_);
return v___x_2203_;
}
}
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_del_object(v___x_2170_);
lean_dec(v_a_2168_);
lean_dec(v_declName_2165_);
lean_dec_ref(v_p_2158_);
lean_dec_ref(v_e_2157_);
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
v___jp_2172_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2175_ = v___x_2170_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_declName_2165_);
lean_dec_ref(v_p_2158_);
lean_dec_ref(v_e_2157_);
v_a_2240_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2167_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2167_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
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
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v___x_2164_);
lean_dec_ref(v_p_2158_);
lean_dec_ref(v_e_2157_);
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStruct_x3f___boxed(lean_object* v_e_2250_, lean_object* v_p_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Meta_etaStruct_x3f(v_e_2250_, v_p_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(lean_object* v_upperBound_2258_, lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v_declName_2261_, lean_object* v___x_2262_, lean_object* v___x_2263_, lean_object* v_a_2264_, lean_object* v_val_2265_, lean_object* v_inst_2266_, lean_object* v_R_2267_, lean_object* v_a_2268_, lean_object* v_b_2269_, lean_object* v_c_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_upperBound_2258_, v___x_2259_, v___x_2260_, v_declName_2261_, v___x_2262_, v___x_2263_, v_a_2264_, v_val_2265_, v_a_2268_, v_b_2269_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2277_ = _args[0];
lean_object* v___x_2278_ = _args[1];
lean_object* v___x_2279_ = _args[2];
lean_object* v_declName_2280_ = _args[3];
lean_object* v___x_2281_ = _args[4];
lean_object* v___x_2282_ = _args[5];
lean_object* v_a_2283_ = _args[6];
lean_object* v_val_2284_ = _args[7];
lean_object* v_inst_2285_ = _args[8];
lean_object* v_R_2286_ = _args[9];
lean_object* v_a_2287_ = _args[10];
lean_object* v_b_2288_ = _args[11];
lean_object* v_c_2289_ = _args[12];
lean_object* v___y_2290_ = _args[13];
lean_object* v___y_2291_ = _args[14];
lean_object* v___y_2292_ = _args[15];
lean_object* v___y_2293_ = _args[16];
lean_object* v___y_2294_ = _args[17];
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(v_upperBound_2277_, v___x_2278_, v___x_2279_, v_declName_2280_, v___x_2281_, v___x_2282_, v_a_2283_, v_val_2284_, v_inst_2285_, v_R_2286_, v_a_2287_, v_b_2288_, v_c_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_val_2284_);
lean_dec(v_a_2283_);
lean_dec(v___x_2281_);
lean_dec(v_declName_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v___x_2278_);
lean_dec(v_upperBound_2277_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(lean_object* v_e_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = l_Lean_Expr_hasMVar(v_e_2296_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_e_2296_);
return v___x_2300_;
}
else
{
lean_object* v___x_2301_; lean_object* v_mctx_2302_; lean_object* v___x_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2306_; lean_object* v_cache_2307_; lean_object* v_zetaDeltaFVarIds_2308_; lean_object* v_postponed_2309_; lean_object* v_diag_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2319_; 
v___x_2301_ = lean_st_ref_get(v___y_2297_);
v_mctx_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc_ref(v_mctx_2302_);
lean_dec(v___x_2301_);
v___x_2303_ = l_Lean_instantiateMVarsCore(v_mctx_2302_, v_e_2296_);
v_fst_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_fst_2304_);
v_snd_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_snd_2305_);
lean_dec_ref(v___x_2303_);
v___x_2306_ = lean_st_ref_take(v___y_2297_);
v_cache_2307_ = lean_ctor_get(v___x_2306_, 1);
v_zetaDeltaFVarIds_2308_ = lean_ctor_get(v___x_2306_, 2);
v_postponed_2309_ = lean_ctor_get(v___x_2306_, 3);
v_diag_2310_ = lean_ctor_get(v___x_2306_, 4);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2306_, 0);
lean_dec(v_unused_2320_);
v___x_2312_ = v___x_2306_;
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_diag_2310_);
lean_inc(v_postponed_2309_);
lean_inc(v_zetaDeltaFVarIds_2308_);
lean_inc(v_cache_2307_);
lean_dec(v___x_2306_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v_snd_2305_);
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_snd_2305_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_cache_2307_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_zetaDeltaFVarIds_2308_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_postponed_2309_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_diag_2310_);
v___x_2315_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_st_ref_put(v___y_2297_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_fst_2304_);
return v___x_2317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(lean_object* v_e_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2321_, v___y_2322_);
lean_dec(v___y_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(lean_object* v_e_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_2325_, v___y_2327_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(lean_object* v_e_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(v_e_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0(lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__0___boxed(lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_Meta_etaStructReduce___lam__0(v_x_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v_x_2349_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1(lean_object* v_p_2356_, lean_object* v_e_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_etaStruct_x3f(v_e_2357_, v_p_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2383_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2383_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
if (lean_obj_tag(v_a_2364_) == 1)
{
lean_object* v_val_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2378_; 
v_val_2368_ = lean_ctor_get(v_a_2364_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_a_2364_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2370_ = v_a_2364_;
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_val_2368_);
lean_dec(v_a_2364_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set_tag(v___x_2370_, 0);
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_val_2368_);
v___x_2373_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2373_);
v___x_2375_ = v___x_2366_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec(v_a_2364_);
v___x_2379_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___lam__0___closed__0));
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2379_);
v___x_2381_ = v___x_2366_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2363_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2363_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___lam__1___boxed(lean_object* v_p_2392_, lean_object* v_e_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_Meta_etaStructReduce___lam__1(v_p_2392_, v_e_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_object* v_00_u03b1_2400_, lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_apply_1(v_x_2401_, lean_box(0));
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(v_00_u03b1_2409_, v_x_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(lean_object* v_a_2417_, lean_object* v_b_2418_, lean_object* v_x_2419_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 0)
{
lean_dec(v_b_2418_);
lean_dec_ref(v_a_2417_);
return v_x_2419_;
}
else
{
lean_object* v_key_2420_; lean_object* v_value_2421_; lean_object* v_tail_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2434_; 
v_key_2420_ = lean_ctor_get(v_x_2419_, 0);
v_value_2421_ = lean_ctor_get(v_x_2419_, 1);
v_tail_2422_ = lean_ctor_get(v_x_2419_, 2);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_x_2419_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2424_ = v_x_2419_;
v_isShared_2425_ = v_isSharedCheck_2434_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_tail_2422_);
lean_inc(v_value_2421_);
lean_inc(v_key_2420_);
lean_dec(v_x_2419_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2434_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
uint8_t v___x_2426_; 
v___x_2426_ = l_Lean_ExprStructEq_beq(v_key_2420_, v_a_2417_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2417_, v_b_2418_, v_tail_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 2, v___x_2427_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_key_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_value_2421_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
else
{
lean_object* v___x_2432_; 
lean_dec(v_value_2421_);
lean_dec(v_key_2420_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v_b_2418_);
lean_ctor_set(v___x_2424_, 0, v_a_2417_);
v___x_2432_ = v___x_2424_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2417_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_b_2418_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_tail_2422_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
if (lean_obj_tag(v_x_2436_) == 0)
{
return v_x_2435_;
}
else
{
lean_object* v_key_2437_; lean_object* v_value_2438_; lean_object* v_tail_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2462_; 
v_key_2437_ = lean_ctor_get(v_x_2436_, 0);
v_value_2438_ = lean_ctor_get(v_x_2436_, 1);
v_tail_2439_ = lean_ctor_get(v_x_2436_, 2);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_x_2436_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2441_ = v_x_2436_;
v_isShared_2442_ = v_isSharedCheck_2462_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_tail_2439_);
lean_inc(v_value_2438_);
lean_inc(v_key_2437_);
lean_dec(v_x_2436_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2462_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; uint64_t v___x_2444_; uint64_t v___x_2445_; uint64_t v___x_2446_; uint64_t v_fold_2447_; uint64_t v___x_2448_; uint64_t v___x_2449_; uint64_t v___x_2450_; size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2443_ = lean_array_get_size(v_x_2435_);
v___x_2444_ = l_Lean_ExprStructEq_hash(v_key_2437_);
v___x_2445_ = 32ULL;
v___x_2446_ = lean_uint64_shift_right(v___x_2444_, v___x_2445_);
v_fold_2447_ = lean_uint64_xor(v___x_2444_, v___x_2446_);
v___x_2448_ = 16ULL;
v___x_2449_ = lean_uint64_shift_right(v_fold_2447_, v___x_2448_);
v___x_2450_ = lean_uint64_xor(v_fold_2447_, v___x_2449_);
v___x_2451_ = lean_uint64_to_usize(v___x_2450_);
v___x_2452_ = lean_usize_of_nat(v___x_2443_);
v___x_2453_ = ((size_t)1ULL);
v___x_2454_ = lean_usize_sub(v___x_2452_, v___x_2453_);
v___x_2455_ = lean_usize_land(v___x_2451_, v___x_2454_);
v___x_2456_ = lean_array_uget_borrowed(v_x_2435_, v___x_2455_);
lean_inc(v___x_2456_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 2, v___x_2456_);
v___x_2458_ = v___x_2441_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_key_2437_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_value_2438_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_array_uset(v_x_2435_, v___x_2455_, v___x_2458_);
v_x_2435_ = v___x_2459_;
v_x_2436_ = v_tail_2439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(lean_object* v_i_2463_, lean_object* v_source_2464_, lean_object* v_target_2465_){
_start:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_array_get_size(v_source_2464_);
v___x_2467_ = lean_nat_dec_lt(v_i_2463_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec_ref(v_source_2464_);
lean_dec(v_i_2463_);
return v_target_2465_;
}
else
{
lean_object* v_es_2468_; lean_object* v___x_2469_; lean_object* v_source_2470_; lean_object* v_target_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_es_2468_ = lean_array_fget(v_source_2464_, v_i_2463_);
v___x_2469_ = lean_box(0);
v_source_2470_ = lean_array_fset(v_source_2464_, v_i_2463_, v___x_2469_);
v_target_2471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_2465_, v_es_2468_);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_add(v_i_2463_, v___x_2472_);
lean_dec(v_i_2463_);
v_i_2463_ = v___x_2473_;
v_source_2464_ = v_source_2470_;
v_target_2465_ = v_target_2471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(lean_object* v_data_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_nbuckets_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2476_ = lean_array_get_size(v_data_2475_);
v___x_2477_ = lean_unsigned_to_nat(2u);
v_nbuckets_2478_ = lean_nat_mul(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_mk_array(v_nbuckets_2478_, v___x_2480_);
v___x_2482_ = lean_array_propagate_mark(v_data_2475_, v___x_2481_);
v___x_2483_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_2479_, v_data_2475_, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(lean_object* v_a_2484_, lean_object* v_x_2485_){
_start:
{
if (lean_obj_tag(v_x_2485_) == 0)
{
uint8_t v___x_2486_; 
v___x_2486_ = 0;
return v___x_2486_;
}
else
{
lean_object* v_key_2487_; lean_object* v_tail_2488_; uint8_t v___x_2489_; 
v_key_2487_ = lean_ctor_get(v_x_2485_, 0);
v_tail_2488_ = lean_ctor_get(v_x_2485_, 2);
v___x_2489_ = l_Lean_ExprStructEq_beq(v_key_2487_, v_a_2484_);
if (v___x_2489_ == 0)
{
v_x_2485_ = v_tail_2488_;
goto _start;
}
else
{
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(lean_object* v_a_2491_, lean_object* v_x_2492_){
_start:
{
uint8_t v_res_2493_; lean_object* v_r_2494_; 
v_res_2493_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_a_2491_);
v_r_2494_ = lean_box(v_res_2493_);
return v_r_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(lean_object* v_m_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v_size_2498_; lean_object* v_buckets_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2542_; 
v_size_2498_ = lean_ctor_get(v_m_2495_, 0);
v_buckets_2499_ = lean_ctor_get(v_m_2495_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_m_2495_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2501_ = v_m_2495_;
v_isShared_2502_ = v_isSharedCheck_2542_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_buckets_2499_);
lean_inc(v_size_2498_);
lean_dec(v_m_2495_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2542_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; uint64_t v___x_2504_; uint64_t v___x_2505_; uint64_t v___x_2506_; uint64_t v_fold_2507_; uint64_t v___x_2508_; uint64_t v___x_2509_; uint64_t v___x_2510_; size_t v___x_2511_; size_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; lean_object* v_bkt_2516_; uint8_t v___x_2517_; 
v___x_2503_ = lean_array_get_size(v_buckets_2499_);
v___x_2504_ = l_Lean_ExprStructEq_hash(v_a_2496_);
v___x_2505_ = 32ULL;
v___x_2506_ = lean_uint64_shift_right(v___x_2504_, v___x_2505_);
v_fold_2507_ = lean_uint64_xor(v___x_2504_, v___x_2506_);
v___x_2508_ = 16ULL;
v___x_2509_ = lean_uint64_shift_right(v_fold_2507_, v___x_2508_);
v___x_2510_ = lean_uint64_xor(v_fold_2507_, v___x_2509_);
v___x_2511_ = lean_uint64_to_usize(v___x_2510_);
v___x_2512_ = lean_usize_of_nat(v___x_2503_);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_sub(v___x_2512_, v___x_2513_);
v___x_2515_ = lean_usize_land(v___x_2511_, v___x_2514_);
v_bkt_2516_ = lean_array_uget_borrowed(v_buckets_2499_, v___x_2515_);
v___x_2517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_2496_, v_bkt_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v_size_x27_2519_; lean_object* v___x_2520_; lean_object* v_buckets_x27_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2518_ = lean_unsigned_to_nat(1u);
v_size_x27_2519_ = lean_nat_add(v_size_2498_, v___x_2518_);
lean_dec(v_size_2498_);
lean_inc(v_bkt_2516_);
v___x_2520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2496_);
lean_ctor_set(v___x_2520_, 1, v_b_2497_);
lean_ctor_set(v___x_2520_, 2, v_bkt_2516_);
v_buckets_x27_2521_ = lean_array_uset(v_buckets_2499_, v___x_2515_, v___x_2520_);
v___x_2522_ = lean_unsigned_to_nat(4u);
v___x_2523_ = lean_nat_mul(v_size_x27_2519_, v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(3u);
v___x_2525_ = lean_nat_div(v___x_2523_, v___x_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_array_get_size(v_buckets_x27_2521_);
v___x_2527_ = lean_nat_dec_le(v___x_2525_, v___x_2526_);
lean_dec(v___x_2525_);
if (v___x_2527_ == 0)
{
lean_object* v_val_2528_; lean_object* v___x_2530_; 
v_val_2528_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_2521_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_val_2528_);
lean_ctor_set(v___x_2501_, 0, v_size_x27_2519_);
v___x_2530_ = v___x_2501_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_size_x27_2519_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_val_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2533_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_buckets_x27_2521_);
lean_ctor_set(v___x_2501_, 0, v_size_x27_2519_);
v___x_2533_ = v___x_2501_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_size_x27_2519_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_buckets_x27_2521_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v___x_2535_; lean_object* v_buckets_x27_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_inc(v_bkt_2516_);
v___x_2535_ = lean_box(0);
v_buckets_x27_2536_ = lean_array_uset(v_buckets_2499_, v___x_2515_, v___x_2535_);
v___x_2537_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_2496_, v_b_2497_, v_bkt_2516_);
v___x_2538_ = lean_array_uset(v_buckets_x27_2536_, v___x_2515_, v___x_2537_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2538_);
v___x_2540_ = v___x_2501_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_size_2498_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(lean_object* v_a_2543_, lean_object* v_e_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = lean_st_ref_take(v_a_2543_);
v___x_2548_ = lean_box(0);
v___x_2549_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_2547_, v_e_2544_, v_a_2545_);
v___x_2550_ = lean_st_ref_put(v_a_2543_, v___x_2549_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(lean_object* v_a_2551_, lean_object* v_e_2552_, lean_object* v_a_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_2551_, v_e_2552_, v_a_2553_);
lean_dec(v_a_2551_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_apply_1(v_x_2557_, lean_box(0));
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_2565_, v_x_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_a_2573_, lean_object* v_x_2574_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = lean_box(0);
return v___x_2575_;
}
else
{
lean_object* v_key_2576_; lean_object* v_value_2577_; lean_object* v_tail_2578_; uint8_t v___x_2579_; 
v_key_2576_ = lean_ctor_get(v_x_2574_, 0);
v_value_2577_ = lean_ctor_get(v_x_2574_, 1);
v_tail_2578_ = lean_ctor_get(v_x_2574_, 2);
v___x_2579_ = l_Lean_ExprStructEq_beq(v_key_2576_, v_a_2573_);
if (v___x_2579_ == 0)
{
v_x_2574_ = v_tail_2578_;
goto _start;
}
else
{
lean_object* v___x_2581_; 
lean_inc(v_value_2577_);
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_value_2577_);
return v___x_2581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_a_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2582_, v_x_2583_);
lean_dec(v_x_2583_);
lean_dec_ref(v_a_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(lean_object* v_m_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_buckets_2587_; lean_object* v___x_2588_; uint64_t v___x_2589_; uint64_t v___x_2590_; uint64_t v___x_2591_; uint64_t v_fold_2592_; uint64_t v___x_2593_; uint64_t v___x_2594_; uint64_t v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_buckets_2587_ = lean_ctor_get(v_m_2585_, 1);
v___x_2588_ = lean_array_get_size(v_buckets_2587_);
v___x_2589_ = l_Lean_ExprStructEq_hash(v_a_2586_);
v___x_2590_ = 32ULL;
v___x_2591_ = lean_uint64_shift_right(v___x_2589_, v___x_2590_);
v_fold_2592_ = lean_uint64_xor(v___x_2589_, v___x_2591_);
v___x_2593_ = 16ULL;
v___x_2594_ = lean_uint64_shift_right(v_fold_2592_, v___x_2593_);
v___x_2595_ = lean_uint64_xor(v_fold_2592_, v___x_2594_);
v___x_2596_ = lean_uint64_to_usize(v___x_2595_);
v___x_2597_ = lean_usize_of_nat(v___x_2588_);
v___x_2598_ = ((size_t)1ULL);
v___x_2599_ = lean_usize_sub(v___x_2597_, v___x_2598_);
v___x_2600_ = lean_usize_land(v___x_2596_, v___x_2599_);
v___x_2601_ = lean_array_uget_borrowed(v_buckets_2587_, v___x_2600_);
v___x_2602_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_2586_, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_2603_, v_a_2604_);
lean_dec_ref(v_a_2604_);
lean_dec_ref(v_m_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(lean_object* v_k_2606_, lean_object* v___y_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
lean_inc(v___y_2612_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v___y_2607_);
v___x_2614_ = lean_apply_7(v_k_2606_, v_b_2608_, v___y_2607_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_2615_, lean_object* v___y_2616_, lean_object* v_b_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_2615_, v___y_2616_, v_b_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2616_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_name_2624_, uint8_t v_bi_2625_, lean_object* v_type_2626_, lean_object* v_k_2627_, uint8_t v_kind_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; 
lean_inc(v___y_2629_);
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2635_, 0, v_k_2627_);
lean_closure_set(v___f_2635_, 1, v___y_2629_);
v___x_2636_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2624_, v_bi_2625_, v_type_2626_, v___f_2635_, v_kind_2628_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2636_) == 0)
{
return v___x_2636_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_name_2645_, lean_object* v_bi_2646_, lean_object* v_type_2647_, lean_object* v_k_2648_, lean_object* v_kind_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_bi_boxed_2656_; uint8_t v_kind_boxed_2657_; lean_object* v_res_2658_; 
v_bi_boxed_2656_ = lean_unbox(v_bi_2646_);
v_kind_boxed_2657_ = lean_unbox(v_kind_2649_);
v_res_2658_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_2645_, v_bi_boxed_2656_, v_type_2647_, v_k_2648_, v_kind_boxed_2657_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(lean_object* v___x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2659_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(lean_object* v___x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(lean_object* v_name_2673_, lean_object* v_type_2674_, lean_object* v_val_2675_, lean_object* v_k_2676_, uint8_t v_nondep_2677_, uint8_t v_kind_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___f_2685_; lean_object* v___x_2686_; 
lean_inc(v___y_2679_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2685_, 0, v_k_2676_);
lean_closure_set(v___f_2685_, 1, v___y_2679_);
v___x_2686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2673_, v_type_2674_, v_val_2675_, v___f_2685_, v_nondep_2677_, v_kind_2678_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2686_) == 0)
{
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(lean_object* v_name_2695_, lean_object* v_type_2696_, lean_object* v_val_2697_, lean_object* v_k_2698_, lean_object* v_nondep_2699_, lean_object* v_kind_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v_nondep_boxed_2707_; uint8_t v_kind_boxed_2708_; lean_object* v_res_2709_; 
v_nondep_boxed_2707_ = lean_unbox(v_nondep_2699_);
v_kind_boxed_2708_ = lean_unbox(v_kind_2700_);
v_res_2709_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_2695_, v_type_2696_, v_val_2697_, v_k_2698_, v_nondep_boxed_2707_, v_kind_boxed_2708_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
return v_res_2709_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = l_Lean_maxRecDepthErrorMessage;
v___x_2716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
v___x_2718_ = l_Lean_MessageData_ofFormat(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
v___x_2720_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2));
v___x_2721_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___x_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(lean_object* v_ref_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_ref_2722_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(lean_object* v_x_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___y_2738_; lean_object* v_toCold_2747_; lean_object* v_currRecDepth_2748_; lean_object* v_ref_2749_; uint16_t v_optionFlags_2750_; uint8_t v_suppressElabErrors_2751_; uint8_t v_checkDeprecated_2752_; uint8_t v_isRecordingDeps_2753_; lean_object* v_maxRecDepth_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_toCold_2747_ = lean_ctor_get(v___y_2734_, 0);
v_currRecDepth_2748_ = lean_ctor_get(v___y_2734_, 1);
v_ref_2749_ = lean_ctor_get(v___y_2734_, 2);
v_optionFlags_2750_ = lean_ctor_get_uint16(v___y_2734_, sizeof(void*)*3);
v_suppressElabErrors_2751_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*3 + 2);
v_checkDeprecated_2752_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2753_ = lean_ctor_get_uint8(v___y_2734_, sizeof(void*)*3 + 4);
v_maxRecDepth_2759_ = lean_ctor_get(v_toCold_2747_, 3);
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_nat_dec_eq(v_maxRecDepth_2759_, v___x_2760_);
if (v___x_2761_ == 0)
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_nat_dec_eq(v_currRecDepth_2748_, v_maxRecDepth_2759_);
if (v___x_2762_ == 0)
{
goto v___jp_2754_;
}
else
{
lean_object* v___x_2763_; 
lean_dec_ref(v_x_2730_);
lean_inc(v_ref_2749_);
v___x_2763_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_2749_);
v___y_2738_ = v___x_2763_;
goto v___jp_2737_;
}
}
else
{
goto v___jp_2754_;
}
v___jp_2737_:
{
if (lean_obj_tag(v___y_2738_) == 0)
{
return v___y_2738_;
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_a_2739_ = lean_ctor_get(v___y_2738_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___y_2738_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___y_2738_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___y_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
v___jp_2754_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_nat_add(v_currRecDepth_2748_, v___x_2755_);
lean_inc(v_ref_2749_);
lean_inc_ref(v_toCold_2747_);
v___x_2757_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2757_, 0, v_toCold_2747_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_ctor_set(v___x_2757_, 2, v_ref_2749_);
lean_ctor_set_uint16(v___x_2757_, sizeof(void*)*3, v_optionFlags_2750_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 2, v_suppressElabErrors_2751_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 3, v_checkDeprecated_2752_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 4, v_isRecordingDeps_2753_);
lean_inc(v___y_2735_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
lean_inc(v___y_2731_);
v___x_2758_ = lean_apply_6(v_x_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___x_2757_, v___y_2735_, lean_box(0));
v___y_2738_ = v___x_2758_;
goto v___jp_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(lean_object* v_fvars_2772_, lean_object* v_pre_2773_, lean_object* v_post_2774_, lean_object* v_usedLetOnly_2775_, lean_object* v_skipConstInApp_2776_, lean_object* v_skipInstances_2777_, lean_object* v_body_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
uint8_t v_usedLetOnly_boxed_2786_; uint8_t v_skipConstInApp_boxed_2787_; uint8_t v_skipInstances_boxed_2788_; lean_object* v_res_2789_; 
v_usedLetOnly_boxed_2786_ = lean_unbox(v_usedLetOnly_2775_);
v_skipConstInApp_boxed_2787_ = lean_unbox(v_skipConstInApp_2776_);
v_skipInstances_boxed_2788_ = lean_unbox(v_skipInstances_2777_);
v_res_2789_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_2772_, v_pre_2773_, v_post_2774_, v_usedLetOnly_boxed_2786_, v_skipConstInApp_boxed_2787_, v_skipInstances_boxed_2788_, v_body_2778_, v_x_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
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
lean_object* v_binderName_2880_; lean_object* v_binderType_2881_; lean_object* v_body_2882_; uint8_t v_binderInfo_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___f_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_binderName_2880_ = lean_ctor_get(v_e_2873_, 0);
lean_inc(v_binderName_2880_);
v_binderType_2881_ = lean_ctor_get(v_e_2873_, 1);
lean_inc_ref(v_binderType_2881_);
v_body_2882_ = lean_ctor_get(v_e_2873_, 2);
lean_inc_ref(v_body_2882_);
v_binderInfo_2883_ = lean_ctor_get_uint8(v_e_2873_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2873_, 3);
v___x_2884_ = lean_box(v_usedLetOnly_2869_);
v___x_2885_ = lean_box(v_skipConstInApp_2870_);
v___x_2886_ = lean_box(v_skipInstances_2871_);
lean_inc_ref(v_post_2868_);
lean_inc_ref(v_pre_2867_);
lean_inc_ref(v_fvars_2872_);
v___f_2887_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2887_, 0, v_fvars_2872_);
lean_closure_set(v___f_2887_, 1, v_pre_2867_);
lean_closure_set(v___f_2887_, 2, v_post_2868_);
lean_closure_set(v___f_2887_, 3, v___x_2884_);
lean_closure_set(v___f_2887_, 4, v___x_2885_);
lean_closure_set(v___f_2887_, 5, v___x_2886_);
lean_closure_set(v___f_2887_, 6, v_body_2882_);
v___x_2888_ = lean_expr_instantiate_rev(v_binderType_2881_, v_fvars_2872_);
lean_dec_ref(v_fvars_2872_);
lean_dec_ref(v_binderType_2881_);
v___x_2889_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2867_, v_post_2868_, v_usedLetOnly_2869_, v_skipConstInApp_2870_, v_skipInstances_2871_, v___x_2888_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = 0;
v___x_2892_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_2880_, v_binderInfo_2883_, v_a_2890_, v___f_2887_, v___x_2891_, v_a_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2892_;
}
else
{
lean_dec_ref(v___f_2887_);
lean_dec(v_binderName_2880_);
return v___x_2889_;
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
lean_object* v_declName_2949_; lean_object* v_type_2950_; lean_object* v_value_2951_; lean_object* v_body_2952_; uint8_t v_nondep_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___f_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
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
v___x_2954_ = lean_box(v_usedLetOnly_2938_);
v___x_2955_ = lean_box(v_skipConstInApp_2939_);
v___x_2956_ = lean_box(v_skipInstances_2940_);
lean_inc_ref_n(v_post_2937_, 2);
lean_inc_ref_n(v_pre_2936_, 2);
lean_inc_ref(v_fvars_2941_);
v___f_2957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2957_, 0, v_fvars_2941_);
lean_closure_set(v___f_2957_, 1, v_pre_2936_);
lean_closure_set(v___f_2957_, 2, v_post_2937_);
lean_closure_set(v___f_2957_, 3, v___x_2954_);
lean_closure_set(v___f_2957_, 4, v___x_2955_);
lean_closure_set(v___f_2957_, 5, v___x_2956_);
lean_closure_set(v___f_2957_, 6, v_body_2952_);
v___x_2958_ = lean_expr_instantiate_rev(v_type_2950_, v_fvars_2941_);
lean_dec_ref(v_type_2950_);
v___x_2959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v___x_2958_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = lean_expr_instantiate_rev(v_value_2951_, v_fvars_2941_);
lean_dec_ref(v_fvars_2941_);
lean_dec_ref(v_value_2951_);
v___x_2962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2936_, v_post_2937_, v_usedLetOnly_2938_, v_skipConstInApp_2939_, v_skipInstances_2940_, v___x_2961_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = 0;
v___x_2965_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_2949_, v_a_2960_, v_a_2963_, v___f_2957_, v_nondep_2953_, v___x_2964_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
return v___x_2965_;
}
else
{
lean_dec(v_a_2960_);
lean_dec_ref(v___f_2957_);
lean_dec(v_declName_2949_);
return v___x_2962_;
}
}
else
{
lean_dec_ref(v___f_2957_);
lean_dec_ref(v_value_2951_);
lean_dec(v_declName_2949_);
lean_dec_ref(v_fvars_2941_);
lean_dec_ref(v_post_2937_);
lean_dec_ref(v_pre_2936_);
return v___x_2959_;
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
lean_object* v_v_2990_; lean_object* v___x_2991_; lean_object* v_bs_x27_2992_; lean_object* v___x_2993_; 
v_v_2990_ = lean_array_uget(v_bs_2981_, v_i_2980_);
v___x_2991_ = lean_unsigned_to_nat(0u);
v_bs_x27_2992_ = lean_array_uset(v_bs_2981_, v_i_2980_, v___x_2991_);
lean_inc_ref(v_post_2975_);
lean_inc_ref(v_pre_2974_);
v___x_2993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_2974_, v_post_2975_, v_usedLetOnly_2976_, v_skipConstInApp_2977_, v_skipInstances_2978_, v_v_2990_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = lean_usize_add(v_i_2980_, v___x_2995_);
v___x_2997_ = lean_array_uset(v_bs_x27_2992_, v_i_2980_, v_a_2994_);
v_i_2980_ = v___x_2996_;
v_bs_2981_ = v___x_2997_;
goto _start;
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_bs_x27_2992_);
lean_dec_ref(v_post_2975_);
lean_dec_ref(v_pre_2974_);
v_a_2999_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2993_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2993_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(lean_object* v_pre_3338_, lean_object* v_post_3339_, uint8_t v_usedLetOnly_3340_, uint8_t v_skipConstInApp_3341_, uint8_t v_skipInstances_3342_, lean_object* v_fvars_3343_, lean_object* v_e_3344_, lean_object* v_a_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
if (lean_obj_tag(v_e_3344_) == 7)
{
lean_object* v_binderName_3351_; lean_object* v_binderType_3352_; lean_object* v_body_3353_; uint8_t v_binderInfo_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___f_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_binderName_3351_ = lean_ctor_get(v_e_3344_, 0);
lean_inc(v_binderName_3351_);
v_binderType_3352_ = lean_ctor_get(v_e_3344_, 1);
lean_inc_ref(v_binderType_3352_);
v_body_3353_ = lean_ctor_get(v_e_3344_, 2);
lean_inc_ref(v_body_3353_);
v_binderInfo_3354_ = lean_ctor_get_uint8(v_e_3344_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3344_, 3);
v___x_3355_ = lean_box(v_usedLetOnly_3340_);
v___x_3356_ = lean_box(v_skipConstInApp_3341_);
v___x_3357_ = lean_box(v_skipInstances_3342_);
lean_inc_ref(v_post_3339_);
lean_inc_ref(v_pre_3338_);
lean_inc_ref(v_fvars_3343_);
v___f_3358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3358_, 0, v_fvars_3343_);
lean_closure_set(v___f_3358_, 1, v_pre_3338_);
lean_closure_set(v___f_3358_, 2, v_post_3339_);
lean_closure_set(v___f_3358_, 3, v___x_3355_);
lean_closure_set(v___f_3358_, 4, v___x_3356_);
lean_closure_set(v___f_3358_, 5, v___x_3357_);
lean_closure_set(v___f_3358_, 6, v_body_3353_);
v___x_3359_ = lean_expr_instantiate_rev(v_binderType_3352_, v_fvars_3343_);
lean_dec_ref(v_fvars_3343_);
lean_dec_ref(v_binderType_3352_);
v___x_3360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v___x_3359_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = 0;
v___x_3363_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_3351_, v_binderInfo_3354_, v_a_3361_, v___f_3358_, v___x_3362_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3363_;
}
else
{
lean_dec_ref(v___f_3358_);
lean_dec(v_binderName_3351_);
return v___x_3360_;
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_expr_instantiate_rev(v_e_3344_, v_fvars_3343_);
lean_dec_ref(v_e_3344_);
lean_inc_ref(v_post_3339_);
lean_inc_ref(v_pre_3338_);
v___x_3365_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v___x_3364_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3365_, 1);
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
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_3338_, v_post_3339_, v_usedLetOnly_3340_, v_skipConstInApp_3341_, v_skipInstances_3342_, v_a_3371_, v_a_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
return v___x_3372_;
}
else
{
lean_dec_ref(v_post_3339_);
lean_dec_ref(v_pre_3338_);
return v___x_3370_;
}
}
else
{
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
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v_a_3395_);
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
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
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
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_a_3431_);
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
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v_a_3448_);
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
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v_a_3465_);
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
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v_a_3482_);
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
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
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
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
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
uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v_a_3550_; lean_object* v___x_3551_; 
v___x_3547_ = 0;
v___x_3548_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
v___x_3549_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3548_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_3538_, v_post_3539_, v_usedLetOnly_3540_, v_skipConstInApp_3541_, v___x_3547_, v_input_3537_, v_a_3550_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3553_, 0, lean_box(0));
lean_closure_set(v___x_3553_, 1, lean_box(0));
lean_closure_set(v___x_3553_, 2, v_a_3550_);
v___x_3554_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(lean_box(0), v___x_3553_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
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
lean_dec(v_a_3550_);
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
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce(lean_object* v_e_3577_, lean_object* v_p_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___x_3586_; lean_object* v_a_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; 
v___f_3584_ = ((lean_object*)(l_Lean_Meta_etaStructReduce___closed__0));
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_Meta_etaStructReduce___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3585_, 0, v_p_3578_);
v___x_3586_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(v_e_3577_, v_a_3580_);
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = 0;
v___x_3589_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(v_a_3587_, v___f_3584_, v___f_3585_, v___x_3588_, v___x_3588_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_etaStructReduce___boxed(lean_object* v_e_3590_, lean_object* v_p_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Meta_etaStructReduce(v_e_3590_, v_p_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
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
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
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
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
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
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
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
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
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
uint8_t v_____do__lift_285__boxed_3797_; lean_object* v_res_3798_; 
v_____do__lift_285__boxed_3797_ = lean_unbox(v_____do__lift_3796_);
v_res_3798_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_3788_, v_usedFields_3789_, v_binderName_3790_, v_body_3791_, v_val_3792_, v_inst_3793_, v_inst_3794_, v_fieldVal_x3f_3795_, v_____do__lift_285__boxed_3797_);
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
lean_inc_n(v_val_3809_, 2);
lean_dec_ref_known(v_____x_3808_, 1);
lean_inc_n(v_inst_3804_, 2);
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
lean_inc_n(v_toBind_3826_, 2);
v_binderName_3832_ = lean_ctor_get(v_e_3824_, 0);
lean_inc_n(v_binderName_3832_, 2);
v_binderType_3833_ = lean_ctor_get(v_e_3824_, 1);
lean_inc_ref(v_binderType_3833_);
v_body_3834_ = lean_ctor_get(v_e_3824_, 2);
lean_inc_ref(v_body_3834_);
lean_dec_ref_known(v_e_3824_, 3);
lean_inc(v_fieldVal_x3f_3822_);
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
lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3843_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3841_);
v___x_3844_ = l_Lean_Expr_isApp(v___x_3843_);
if (v___x_3844_ == 0)
{
lean_dec_ref(v___x_3843_);
lean_dec_ref(v___x_3841_);
lean_del_object(v___x_3839_);
goto v___jp_3828_;
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3843_);
lean_dec_ref(v___x_3843_);
v___x_3846_ = ((lean_object*)(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1));
v___x_3847_ = l_Lean_Expr_isConstOf(v___x_3845_, v___x_3846_);
lean_dec_ref(v___x_3845_);
if (v___x_3847_ == 0)
{
lean_dec_ref(v___x_3841_);
lean_del_object(v___x_3839_);
goto v___jp_3828_;
}
else
{
lean_object* v_arg_3848_; lean_object* v___x_3850_; 
lean_dec_ref(v_e_3824_);
v_arg_3848_ = lean_ctor_get(v___x_3841_, 1);
lean_inc_ref(v_arg_3848_);
lean_dec_ref(v___x_3841_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 1, v_arg_3848_);
lean_ctor_set(v___x_3839_, 0, v_usedFields_3823_);
v___x_3850_ = v___x_3839_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_usedFields_3823_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_arg_3848_);
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
lean_dec_ref_known(v_fst_3883_, 1);
v___x_3888_ = lean_apply_2(v_toPure_3881_, lean_box(0), v_val_3887_);
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(lean_object* v_body_3889_, lean_object* v_a_3890_, lean_object* v___x_3891_, lean_object* v_toPure_3892_, lean_object* v_____r_3893_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3894_ = lean_expr_instantiate1(v_body_3889_, v_a_3890_);
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3891_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
v___x_3897_ = lean_apply_2(v_toPure_3892_, lean_box(0), v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(lean_object* v_body_3898_, lean_object* v_a_3899_, lean_object* v___x_3900_, lean_object* v_toPure_3901_, lean_object* v_____r_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3898_, v_a_3899_, v___x_3900_, v_toPure_3901_, v_____r_3902_);
lean_dec_ref(v_a_3899_);
lean_dec_ref(v_body_3898_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(lean_object* v_snd_3906_, lean_object* v_toPure_3907_, lean_object* v___f_3908_, uint8_t v_____do__lift_3909_){
_start:
{
if (v_____do__lift_3909_ == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_dec(v___f_3908_);
v___x_3910_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
lean_ctor_set(v___x_3911_, 1, v_snd_3906_);
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___x_3913_ = lean_apply_2(v_toPure_3907_, lean_box(0), v___x_3912_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec(v_toPure_3907_);
lean_dec(v_snd_3906_);
v___x_3914_ = lean_box(0);
v___x_3915_ = lean_apply_1(v___f_3908_, v___x_3914_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(lean_object* v_snd_3916_, lean_object* v_toPure_3917_, lean_object* v___f_3918_, lean_object* v_____do__lift_3919_){
_start:
{
uint8_t v_____do__lift_566__boxed_3920_; lean_object* v_res_3921_; 
v_____do__lift_566__boxed_3920_ = lean_unbox(v_____do__lift_3919_);
v_res_3921_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(v_snd_3916_, v_toPure_3917_, v___f_3918_, v_____do__lift_566__boxed_3920_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(lean_object* v_binderType_3922_, lean_object* v_inst_3923_, lean_object* v_toBind_3924_, lean_object* v___f_3925_, lean_object* v_____do__lift_3926_){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_alloc_closure((void*)(l_Lean_Meta_isDefEq___boxed), 7, 2);
lean_closure_set(v___x_3927_, 0, v_____do__lift_3926_);
lean_closure_set(v___x_3927_, 1, v_binderType_3922_);
v___x_3928_ = lean_apply_2(v_inst_3923_, lean_box(0), v___x_3927_);
v___x_3929_ = lean_apply_4(v_toBind_3924_, lean_box(0), lean_box(0), v___x_3928_, v___f_3925_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(lean_object* v___x_3930_, lean_object* v_toPure_3931_, lean_object* v_levels_x3f_3932_, lean_object* v_inst_3933_, lean_object* v_toBind_3934_, lean_object* v_a_3935_, lean_object* v_x_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_snd_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3958_; 
v_snd_3938_ = lean_ctor_get(v___y_3937_, 1);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___y_3937_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v___y_3937_, 0);
lean_dec(v_unused_3959_);
v___x_3940_ = v___y_3937_;
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_snd_3938_);
lean_dec(v___y_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
if (lean_obj_tag(v_snd_3938_) == 6)
{
lean_object* v_binderType_3942_; lean_object* v_body_3943_; lean_object* v___f_3944_; 
lean_del_object(v___x_3940_);
v_binderType_3942_ = lean_ctor_get(v_snd_3938_, 1);
lean_inc_ref(v_binderType_3942_);
v_body_3943_ = lean_ctor_get(v_snd_3938_, 2);
lean_inc(v_toPure_3931_);
lean_inc(v___x_3930_);
lean_inc_ref(v_a_3935_);
lean_inc_ref(v_body_3943_);
v___f_3944_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3944_, 0, v_body_3943_);
lean_closure_set(v___f_3944_, 1, v_a_3935_);
lean_closure_set(v___f_3944_, 2, v___x_3930_);
lean_closure_set(v___f_3944_, 3, v_toPure_3931_);
if (lean_obj_tag(v_levels_x3f_3932_) == 0)
{
lean_object* v___f_3945_; lean_object* v___f_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v___x_3930_);
v___f_3945_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3945_, 0, v_snd_3938_);
lean_closure_set(v___f_3945_, 1, v_toPure_3931_);
lean_closure_set(v___f_3945_, 2, v___f_3944_);
lean_inc(v_toBind_3934_);
lean_inc(v_inst_3933_);
v___f_3946_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3946_, 0, v_binderType_3942_);
lean_closure_set(v___f_3946_, 1, v_inst_3933_);
lean_closure_set(v___f_3946_, 2, v_toBind_3934_);
lean_closure_set(v___f_3946_, 3, v___f_3945_);
v___x_3947_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_3947_, 0, v_a_3935_);
v___x_3948_ = lean_apply_2(v_inst_3933_, lean_box(0), v___x_3947_);
v___x_3949_ = lean_apply_4(v_toBind_3934_, lean_box(0), lean_box(0), v___x_3948_, v___f_3946_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_inc_ref(v_body_3943_);
lean_dec_ref(v___f_3944_);
lean_dec_ref(v_binderType_3942_);
lean_dec_ref_known(v_snd_3938_, 3);
lean_dec(v_toBind_3934_);
lean_dec(v_inst_3933_);
v___x_3950_ = lean_box(0);
v___x_3951_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(v_body_3943_, v_a_3935_, v___x_3930_, v_toPure_3931_, v___x_3950_);
lean_dec_ref(v_a_3935_);
lean_dec_ref(v_body_3943_);
return v___x_3951_;
}
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
lean_dec_ref(v_a_3935_);
lean_dec(v_toBind_3934_);
lean_dec(v_inst_3933_);
lean_dec(v___x_3930_);
v___x_3952_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0));
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3952_);
v___x_3954_ = v___x_3940_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_snd_3938_);
v___x_3954_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
v___x_3956_ = lean_apply_2(v_toPure_3931_, lean_box(0), v___x_3955_);
return v___x_3956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(lean_object* v___x_3960_, lean_object* v_toPure_3961_, lean_object* v_levels_x3f_3962_, lean_object* v_inst_3963_, lean_object* v_toBind_3964_, lean_object* v_a_3965_, lean_object* v_x_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(v___x_3960_, v_toPure_3961_, v_levels_x3f_3962_, v_inst_3963_, v_toBind_3964_, v_a_3965_, v_x_3966_, v___y_3967_);
lean_dec(v_levels_x3f_3962_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(lean_object* v_toPure_3969_, lean_object* v_levels_x3f_3970_, lean_object* v_inst_3971_, lean_object* v_toBind_3972_, lean_object* v_params_3973_, lean_object* v_inst_3974_, lean_object* v___f_3975_, lean_object* v_val_3976_){
_start:
{
lean_object* v___x_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; size_t v_sz_3980_; size_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3977_ = lean_box(0);
lean_inc(v_toBind_3972_);
v___f_3978_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_3978_, 0, v___x_3977_);
lean_closure_set(v___f_3978_, 1, v_toPure_3969_);
lean_closure_set(v___f_3978_, 2, v_levels_x3f_3970_);
lean_closure_set(v___f_3978_, 3, v_inst_3971_);
lean_closure_set(v___f_3978_, 4, v_toBind_3972_);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v_val_3976_);
v_sz_3980_ = lean_array_size(v_params_3973_);
v___x_3981_ = ((size_t)0ULL);
v___x_3982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3974_, v_params_3973_, v___f_3978_, v_sz_3980_, v___x_3981_, v___x_3979_);
v___x_3983_ = lean_apply_4(v_toBind_3972_, lean_box(0), lean_box(0), v___x_3982_, v___f_3975_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(lean_object* v_cinfo_3984_, lean_object* v_us_3985_, uint8_t v___x_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Lean_Core_instantiateValueLevelParams(v_cinfo_3984_, v_us_3985_, v___x_3986_, v___y_3989_, v___y_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(lean_object* v_cinfo_3993_, lean_object* v_us_3994_, lean_object* v___x_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
uint8_t v___x_677__boxed_4001_; lean_object* v_res_4002_; 
v___x_677__boxed_4001_ = lean_unbox(v___x_3995_);
v_res_4002_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(v_cinfo_3993_, v_us_3994_, v___x_677__boxed_4001_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v_cinfo_3993_);
return v_res_4002_;
}
}
static lean_object* _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4006_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2));
v___x_4007_ = lean_unsigned_to_nat(2u);
v___x_4008_ = lean_unsigned_to_nat(202u);
v___x_4009_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1));
v___x_4010_ = ((lean_object*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0));
v___x_4011_ = l_mkPanicMessageWithDecl(v___x_4010_, v___x_4009_, v___x_4008_, v___x_4007_, v___x_4006_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(lean_object* v_cinfo_4012_, lean_object* v___x_4013_, lean_object* v_inst_4014_, lean_object* v_toBind_4015_, lean_object* v___f_4016_, lean_object* v_us_4017_){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4018_ = l_List_lengthTR___redArg(v_us_4017_);
v___x_4019_ = l_Lean_ConstantInfo_levelParams(v_cinfo_4012_);
v___x_4020_ = l_List_lengthTR___redArg(v___x_4019_);
lean_dec(v___x_4019_);
v___x_4021_ = lean_nat_dec_eq(v___x_4018_, v___x_4020_);
lean_dec(v___x_4020_);
lean_dec(v___x_4018_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec(v_us_4017_);
lean_dec(v___f_4016_);
lean_dec(v_toBind_4015_);
lean_dec(v_inst_4014_);
lean_dec_ref(v_cinfo_4012_);
v___x_4022_ = lean_obj_once(&l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3, &l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once, _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3);
v___x_4023_ = l_panic___redArg(v___x_4013_, v___x_4022_);
return v___x_4023_;
}
else
{
uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___f_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4024_ = 0;
v___x_4025_ = lean_box(v___x_4024_);
v___f_4026_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed), 8, 3);
lean_closure_set(v___f_4026_, 0, v_cinfo_4012_);
lean_closure_set(v___f_4026_, 1, v_us_4017_);
lean_closure_set(v___f_4026_, 2, v___x_4025_);
v___x_4027_ = lean_apply_2(v_inst_4014_, lean_box(0), v___f_4026_);
v___x_4028_ = lean_apply_4(v_toBind_4015_, lean_box(0), lean_box(0), v___x_4027_, v___f_4016_);
return v___x_4028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed(lean_object* v_cinfo_4029_, lean_object* v___x_4030_, lean_object* v_inst_4031_, lean_object* v_toBind_4032_, lean_object* v___f_4033_, lean_object* v_us_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(v_cinfo_4029_, v___x_4030_, v_inst_4031_, v_toBind_4032_, v___f_4033_, v_us_4034_);
lean_dec(v___x_4030_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(lean_object* v___x_4036_, lean_object* v_inst_4037_, lean_object* v_toBind_4038_, lean_object* v___f_4039_, lean_object* v_levels_x3f_4040_, lean_object* v_toPure_4041_, lean_object* v_cinfo_4042_){
_start:
{
lean_object* v___f_4043_; 
lean_inc(v_toBind_4038_);
lean_inc(v_inst_4037_);
lean_inc_ref(v_cinfo_4042_);
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_4043_, 0, v_cinfo_4042_);
lean_closure_set(v___f_4043_, 1, v___x_4036_);
lean_closure_set(v___f_4043_, 2, v_inst_4037_);
lean_closure_set(v___f_4043_, 3, v_toBind_4038_);
lean_closure_set(v___f_4043_, 4, v___f_4039_);
if (lean_obj_tag(v_levels_x3f_4040_) == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_dec(v_toPure_4041_);
v___x_4044_ = lean_alloc_closure((void*)(l_Lean_Meta_mkFreshLevelMVarsFor___boxed), 6, 1);
lean_closure_set(v___x_4044_, 0, v_cinfo_4042_);
v___x_4045_ = lean_apply_2(v_inst_4037_, lean_box(0), v___x_4044_);
v___x_4046_ = lean_apply_4(v_toBind_4038_, lean_box(0), lean_box(0), v___x_4045_, v___f_4043_);
return v___x_4046_;
}
else
{
lean_object* v_val_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec_ref(v_cinfo_4042_);
lean_dec(v_inst_4037_);
v_val_4047_ = lean_ctor_get(v_levels_x3f_4040_, 0);
lean_inc(v_val_4047_);
lean_dec_ref_known(v_levels_x3f_4040_, 1);
v___x_4048_ = lean_apply_2(v_toPure_4041_, lean_box(0), v_val_4047_);
v___x_4049_ = lean_apply_4(v_toBind_4038_, lean_box(0), lean_box(0), v___x_4048_, v___f_4043_);
return v___x_4049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_defaultFn_4054_, lean_object* v_levels_x3f_4055_, lean_object* v_params_4056_, lean_object* v_fieldVal_x3f_4057_){
_start:
{
lean_object* v_toApplicative_4058_; lean_object* v_toBind_4059_; lean_object* v_toPure_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___f_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; lean_object* v___f_4066_; lean_object* v___x_4067_; 
v_toApplicative_4058_ = lean_ctor_get(v_inst_4050_, 0);
v_toBind_4059_ = lean_ctor_get(v_inst_4050_, 1);
lean_inc_n(v_toBind_4059_, 3);
v_toPure_4060_ = lean_ctor_get(v_toApplicative_4058_, 1);
lean_inc_n(v_toPure_4060_, 3);
v___x_4061_ = lean_box(0);
lean_inc_ref_n(v_inst_4050_, 3);
v___x_4062_ = l_Lean_getConstInfo___redArg(v_inst_4050_, v_inst_4051_, v_inst_4052_, v_defaultFn_4054_);
lean_inc_n(v_inst_4053_, 2);
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_4063_, 0, v_inst_4050_);
lean_closure_set(v___f_4063_, 1, v_inst_4053_);
lean_closure_set(v___f_4063_, 2, v_fieldVal_x3f_4057_);
lean_closure_set(v___f_4063_, 3, v_toPure_4060_);
lean_inc(v_levels_x3f_4055_);
v___f_4064_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5), 8, 7);
lean_closure_set(v___f_4064_, 0, v_toPure_4060_);
lean_closure_set(v___f_4064_, 1, v_levels_x3f_4055_);
lean_closure_set(v___f_4064_, 2, v_inst_4053_);
lean_closure_set(v___f_4064_, 3, v_toBind_4059_);
lean_closure_set(v___f_4064_, 4, v_params_4056_);
lean_closure_set(v___f_4064_, 5, v_inst_4050_);
lean_closure_set(v___f_4064_, 6, v___f_4063_);
v___x_4065_ = l_instInhabitedOfMonad___redArg(v_inst_4050_, v___x_4061_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8), 7, 6);
lean_closure_set(v___f_4066_, 0, v___x_4065_);
lean_closure_set(v___f_4066_, 1, v_inst_4053_);
lean_closure_set(v___f_4066_, 2, v_toBind_4059_);
lean_closure_set(v___f_4066_, 3, v___f_4064_);
lean_closure_set(v___f_4066_, 4, v_levels_x3f_4055_);
lean_closure_set(v___f_4066_, 5, v_toPure_4060_);
v___x_4067_ = lean_apply_4(v_toBind_4059_, lean_box(0), lean_box(0), v___x_4062_, v___f_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f(lean_object* v_m_4068_, lean_object* v_inst_4069_, lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_inst_4072_, lean_object* v_inst_4073_, lean_object* v_defaultFn_4074_, lean_object* v_levels_x3f_4075_, lean_object* v_params_4076_, lean_object* v_fieldVal_x3f_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(v_inst_4069_, v_inst_4070_, v_inst_4071_, v_inst_4072_, v_defaultFn_4074_, v_levels_x3f_4075_, v_params_4076_, v_fieldVal_x3f_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(lean_object* v_m_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_inst_4084_, lean_object* v_defaultFn_4085_, lean_object* v_levels_x3f_4086_, lean_object* v_params_4087_, lean_object* v_fieldVal_x3f_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(v_m_4079_, v_inst_4080_, v_inst_4081_, v_inst_4082_, v_inst_4083_, v_inst_4084_, v_defaultFn_4085_, v_levels_x3f_4086_, v_params_4087_, v_fieldVal_x3f_4088_);
lean_dec_ref(v_inst_4084_);
return v_res_4089_;
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
